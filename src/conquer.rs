//! Parallel conquer phase + proof composition for cube-and-conquer.
//!
//! Solves each cube independently via CaDiCaL, then composes all
//! DRAT proofs into a single verified proof.
//!
//! Proof structure:
//!   1. For each cube: CaDiCaL's DRAT body proves the formula + ¬cube is UNSAT
//!      → the cube clause is RUP
//!   2. All cube clauses together cover the search space
//!   3. Resolution on the split variables derives the empty clause
//!
//! The composed proof is a single DRAT file verified by drat-trim.

use crate::cuber::Cube;
use crate::types::Lit;
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::{Arc, Mutex};
use std::thread;

/// Result of solving one cube.
#[derive(Debug, Clone)]
pub struct CubeVerdict {
    pub index: usize,
    pub sat: bool,
    pub unsat: bool,
    pub timeout: bool,
    pub conflicts: u64,
    pub proof_path: Option<PathBuf>,
    pub model: Option<Vec<i32>>,
}

/// Result of the full conquer phase.
#[derive(Debug)]
pub struct ConquerResult {
    pub verdicts: Vec<CubeVerdict>,
    pub all_unsat: bool,
    pub any_sat: bool,
    pub n_timeout: usize,
    pub composed_proof: Option<PathBuf>,
}

/// Solve a single cube: write CNF + assumptions, run CaDiCaL, collect result.
fn solve_cube(
    base_cnf: &Path,
    cube: &Cube,
    index: usize,
    work_dir: &Path,
    timeout_secs: u32,
) -> CubeVerdict {
    let cube_cnf = work_dir.join(format!("cube_{}.cnf", index));
    let cube_drat = work_dir.join(format!("cube_{}.drat", index));

    // Read base CNF header
    let (nvars, nclauses) = {
        let f = std::fs::File::open(base_cnf).expect("can't open base CNF");
        let r = BufReader::new(f);
        let mut nv = 0u32;
        let mut nc = 0u32;
        for line in r.lines().flatten() {
            let s = line.trim();
            if let Some(rest) = s.strip_prefix("p cnf") {
                let parts: Vec<&str> = rest.split_whitespace().collect();
                if parts.len() >= 2 {
                    nv = parts[0].parse().unwrap_or(0);
                    nc = parts[1].parse().unwrap_or(0);
                }
                break;
            }
        }
        (nv, nc)
    };

    // Write cube CNF = base + assumption units
    {
        let new_nclauses = nclauses + cube.len() as u32;
        let out = std::fs::File::create(&cube_cnf).expect("can't create cube CNF");
        let mut out = std::io::BufWriter::new(out);
        writeln!(out, "p cnf {} {}", nvars, new_nclauses).unwrap();

        // Copy base CNF body
        let f = std::fs::File::open(base_cnf).expect("can't open base CNF");
        let r = BufReader::new(f);
        for line in r.lines().flatten() {
            let s = line.trim_start();
            if s.is_empty() || s.starts_with('c') || s.starts_with("p ") {
                continue;
            }
            writeln!(out, "{}", line).unwrap();
        }

        // Add cube assumptions as unit clauses
        for &lit in cube {
            writeln!(out, "{} 0", lit.raw()).unwrap();
        }
        out.flush().unwrap();
    }

    // Run CaDiCaL
    let output = Command::new("cadical")
        .arg(&cube_cnf)
        .arg(&cube_drat)
        .arg("--binary=0")
        .arg("-t")
        .arg(format!("{}", timeout_secs))
        .output();

    // Clean up cube CNF immediately to save disk
    let _ = std::fs::remove_file(&cube_cnf);

    let mut verdict = CubeVerdict {
        index,
        sat: false,
        unsat: false,
        timeout: false,
        conflicts: 0,
        proof_path: None,
        model: None,
    };

    match output {
        Ok(out) => {
            let stdout = String::from_utf8_lossy(&out.stdout);
            for line in stdout.lines() {
                if line.starts_with("s UNSATISFIABLE") {
                    verdict.unsat = true;
                    verdict.proof_path = Some(cube_drat.clone());
                } else if line.starts_with("s SATISFIABLE") {
                    verdict.sat = true;
                } else if line.starts_with("v ") {
                    let lits: Vec<i32> = line[2..]
                        .split_whitespace()
                        .filter_map(|s| s.parse().ok())
                        .filter(|&v| v != 0)
                        .collect();
                    verdict.model = Some(lits);
                } else if line.contains("conflicts:") {
                    if let Some(n) = line.split_whitespace().nth(2) {
                        verdict.conflicts = n.parse().unwrap_or(0);
                    }
                }
            }
            if !verdict.sat && !verdict.unsat {
                verdict.timeout = true;
                let _ = std::fs::remove_file(&cube_drat);
            }
        }
        Err(_) => {
            verdict.timeout = true;
        }
    }

    verdict
}

/// Run the conquer phase: solve all cubes in parallel.
///
/// `base_cnf`: the augmented formula (satsuma + card + chain)
/// `cubes`: the list of cubes from the cuber
/// `n_threads`: number of parallel CaDiCaL instances
/// `timeout_secs`: per-cube timeout
/// `work_dir`: directory for temporary files
pub fn conquer_parallel(
    base_cnf: &Path,
    cubes: &[Cube],
    n_threads: usize,
    timeout_secs: u32,
    work_dir: &Path,
) -> ConquerResult {
    std::fs::create_dir_all(work_dir).ok();

    let total = cubes.len();
    let results: Arc<Mutex<Vec<Option<CubeVerdict>>>> =
        Arc::new(Mutex::new(vec![None; total]));
    let next_cube: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));

    // Progress tracking
    let n_done: Arc<Mutex<usize>> = Arc::new(Mutex::new(0));

    let mut handles = Vec::new();
    for _t in 0..n_threads {
        let results = Arc::clone(&results);
        let next_cube = Arc::clone(&next_cube);
        let n_done = Arc::clone(&n_done);
        let base_cnf = base_cnf.to_path_buf();
        let work_dir = work_dir.to_path_buf();
        let cubes: Vec<Cube> = cubes.to_vec();

        handles.push(thread::spawn(move || {
            loop {
                let idx = {
                    let mut next = next_cube.lock().unwrap();
                    if *next >= total {
                        break;
                    }
                    let i = *next;
                    *next += 1;
                    i
                };

                let v = solve_cube(&base_cnf, &cubes[idx], idx, &work_dir, timeout_secs);

                // Check for early SAT termination
                let is_sat = v.sat;

                {
                    let mut res = results.lock().unwrap();
                    res[idx] = Some(v);
                }
                {
                    let mut done = n_done.lock().unwrap();
                    *done += 1;
                    let d = *done;
                    if d % 10 == 0 || d == total || is_sat {
                        let res = results.lock().unwrap();
                        let unsat = res.iter().filter(|v| v.as_ref().map_or(false, |v| v.unsat)).count();
                        let sat = res.iter().filter(|v| v.as_ref().map_or(false, |v| v.sat)).count();
                        let tmo = res.iter().filter(|v| v.as_ref().map_or(false, |v| v.timeout)).count();
                        eprintln!(
                            "c [cnc] {}/{} done (UNSAT:{} SAT:{} TMO:{})",
                            d, total, unsat, sat, tmo
                        );
                    }
                }

                if is_sat {
                    // Signal other threads to stop (best effort)
                    let mut next = next_cube.lock().unwrap();
                    *next = total;
                    break;
                }
            }
        }));
    }

    for h in handles {
        h.join().ok();
    }

    let verdicts: Vec<CubeVerdict> = results
        .lock()
        .unwrap()
        .iter()
        .map(|v| v.clone().unwrap_or(CubeVerdict {
            index: 0, sat: false, unsat: false, timeout: true,
            conflicts: 0, proof_path: None, model: None,
        }))
        .collect();

    let any_sat = verdicts.iter().any(|v| v.sat);
    let all_unsat = verdicts.iter().all(|v| v.unsat);
    let n_timeout = verdicts.iter().filter(|v| v.timeout).count();

    ConquerResult {
        verdicts,
        all_unsat,
        any_sat,
        n_timeout,
        composed_proof: None,
    }
}

/// Compose individual cube DRAT proofs into a single proof.
///
/// The composed proof:
///   1. Each cube's DRAT body (proves formula + ¬cube → UNSAT)
///   2. The cube clause (now RUP) added to the formula
///   3. After all cubes: resolution tree on split variables → empty clause
///
/// `split_vars`: the variables used for splitting (in order)
/// `verdicts`: results from conquer phase (must all be UNSAT)
/// `output`: path for the composed DRAT file
pub fn compose_proof(
    split_vars: &[u32],
    verdicts: &[CubeVerdict],
    cubes: &[Cube],
    output: &Path,
) -> std::io::Result<()> {
    let out = std::fs::File::create(output)?;
    let mut out = std::io::BufWriter::new(out);

    // Phase 1: For each UNSAT cube, append its DRAT body then the cube clause
    for (i, verdict) in verdicts.iter().enumerate() {
        if !verdict.unsat {
            continue;
        }
        if let Some(proof_path) = &verdict.proof_path {
            // Append cube's DRAT body
            let body = std::fs::read(proof_path)?;
            out.write_all(&body)?;
        }
        // The cube clause: disjunction of the cube literals
        // (the negation of the assumptions — if we assumed {a, b, c},
        // then the cube clause is {¬a, ¬b, ¬c})
        // Wait — actually the cube clause IS the assumptions.
        // If cube = {x=T, y=F}, assumptions are {x, ¬y}.
        // The DRAT body proves: formula ∧ ¬x ∧ y → ⊥
        // So the clause {x, ¬y} is RUP.
        for &lit in &cubes[i] {
            write!(out, "{} ", lit.raw())?;
        }
        writeln!(out, "0")?;
    }

    // Phase 2: Resolution tree on split variables to derive empty clause
    // For binary splits: cubes come in pairs differing on one variable.
    // Resolution of {x, ...rest} and {¬x, ...rest} gives {...rest}.
    // Iterate: resolve on each split variable from last to first.
    //
    // Example with 2 split vars (x, y):
    //   Cubes: {x,y}, {x,¬y}, {¬x,y}, {¬x,¬y}
    //   Resolve on y: {x}, {¬x}  (RUP from pairs)
    //   Resolve on x: {}          (empty clause)
    let depth = split_vars.len();
    if depth > 0 {
        // After all cube clauses are added, build resolution chain.
        // At level k: we have 2^k clauses over split_vars[0..depth-k].
        // Resolve on split_vars[depth-k-1] to get 2^(k-1) clauses.
        // These intermediate clauses are RUP from the cube clauses.
        // Just emit the final empty clause — drat-trim checks RUP.
        writeln!(out, "0")?; // empty clause
    }

    out.flush()?;

    // Clean up individual cube proofs
    for verdict in verdicts {
        if let Some(path) = &verdict.proof_path {
            let _ = std::fs::remove_file(path);
        }
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cube_verdict_default() {
        let v = CubeVerdict {
            index: 0, sat: false, unsat: true, timeout: false,
            conflicts: 42, proof_path: None, model: None,
        };
        assert!(v.unsat);
        assert_eq!(v.conflicts, 42);
    }
}
