//! Cascade CLI — Week 3: satsuma symmetry breaking → CaDiCaL backend.
//!
//! Usage:
//!   cascade <input.cnf> [--proof out.drat] [--equisat-proof out.pbp]
//!                       [--timeout SECS] [--no-solve] [--no-symmetry]
//!
//! Pipeline:
//!   1. Parse CNF
//!   2. (unless --no-symmetry) run satsuma → augmented CNF + VeriPB equisat proof
//!   3. (unless --no-solve) run CaDiCaL on the augmented CNF → DRAT body proof
//!
//! Two-file proof: --equisat-proof and --proof together prove the BARE CNF
//! is UNSAT (or SAT with the model).

use cascade::backend::cadical::CaDiCaL;
use cascade::backend::{Backend, BackendProofFormat, Verdict};
use cascade::bcp::{bcp_cascade, BcpResult};
use cascade::cardinality;
use cascade::certify;
use cascade::dimacs;
use cascade::symmetry::satsuma::Satsuma;
use cascade::symmetry::{EquisatProofFormat, SymmetryBreaker};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

fn print_usage(prog: &str) {
    eprintln!(
        "Usage: {} <input.cnf> [--proof <out.drat>] [--equisat-proof <out.pbp>]\n\
        \x20            [--timeout <secs>] [--no-solve] [--no-symmetry]",
        prog
    );
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage(&args[0]);
        return ExitCode::from(2);
    }

    let mut input: Option<PathBuf> = None;
    let mut proof: Option<PathBuf> = None;
    let mut equisat_proof: Option<PathBuf> = None;
    let mut timeout: Option<u32> = None;
    let mut no_solve = false;
    let mut no_symmetry = false;
    let mut no_card = false;
    let mut no_bcp = false;
    let mut certified = false;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--proof" => {
                if i + 1 >= args.len() {
                    eprintln!("--proof needs an argument");
                    return ExitCode::from(2);
                }
                proof = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--equisat-proof" => {
                if i + 1 >= args.len() {
                    eprintln!("--equisat-proof needs an argument");
                    return ExitCode::from(2);
                }
                equisat_proof = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--timeout" => {
                if i + 1 >= args.len() {
                    eprintln!("--timeout needs an argument");
                    return ExitCode::from(2);
                }
                timeout = Some(args[i + 1].parse().unwrap_or(0));
                i += 2;
            }
            "--no-solve" => {
                no_solve = true;
                i += 1;
            }
            "--no-symmetry" => {
                no_symmetry = true;
                i += 1;
            }
            "--no-card" => {
                no_card = true;
                i += 1;
            }
            "--no-bcp" => {
                no_bcp = true;
                i += 1;
            }
            "--certified" => {
                certified = true;
                i += 1;
            }
            "-h" | "--help" => {
                print_usage(&args[0]);
                return ExitCode::SUCCESS;
            }
            other => {
                if input.is_some() {
                    eprintln!("unexpected argument: {}", other);
                    return ExitCode::from(2);
                }
                input = Some(PathBuf::from(other));
                i += 1;
            }
        }
    }

    let input = match input {
        Some(p) => p,
        None => {
            print_usage(&args[0]);
            return ExitCode::from(2);
        }
    };

    let cnf = match dimacs::parse_file(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("parse error: {}", e);
            return ExitCode::from(1);
        }
    };

    // Under --certified, auto-generate proof paths if not provided
    if certified {
        if proof.is_none() {
            proof = Some(scratch_path(&input, "_body.drat"));
        }
        if equisat_proof.is_none() {
            equisat_proof = Some(scratch_path(&input, "_equisat.pbp"));
        }
    }

    println!(
        "c cascade — parsed {} vars, {} clauses{}",
        cnf.nvars,
        cnf.clauses.len(),
        if certified { " [CERTIFIED MODE]" } else { "" }
    );

    // === Stage 1: Symmetry breaking via satsuma ===
    let mut effective_cnf: PathBuf = input.clone();
    let pre_card_cnf: PathBuf;
    if !no_symmetry {
        let breaker = Satsuma::new();
        let aug = scratch_path(&input, "_aug.cnf");
        let proof_target = equisat_proof.clone().or_else(|| {
            if proof.is_some() {
                Some(scratch_path(&input, "_equisat.pbp"))
            } else {
                None
            }
        });
        let format = if proof_target.is_some() {
            EquisatProofFormat::VeriPb
        } else {
            EquisatProofFormat::None
        };
        match breaker.break_symmetries(&input, &aug, proof_target.as_deref(), format) {
            Ok(r) => {
                println!(
                    "c [{}] {} gens, {} sbp clauses, {} aux vars ({:.2}s)",
                    breaker.name(),
                    r.n_generators,
                    r.n_sbp_clauses,
                    r.n_aux_vars,
                    r.elapsed_secs
                );
                if let Some(p) = &r.equisat_proof {
                    println!("c [{}] equisat proof: {}", breaker.name(), p.display());
                    if certified {
                        print!("c [certify] veripb equisat... ");
                        match certify::verify_veripb(&input, p) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                eprintln!("c [certify] FATAL: equisat proof rejected");
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
                effective_cnf = r.augmented_cnf;
            }
            Err(e) => {
                eprintln!(
                    "c [satsuma] error: {} — falling back to bare CNF",
                    e
                );
            }
        }
    }

    // Save state for certified mode proof combination
    pre_card_cnf = effective_cnf.clone();
    let mut card_clauses: Vec<Vec<cascade::types::Lit>> = Vec::new();

    // === Stage 1b: Cardinality CNF augmentation (Ramsey degree bounds) ===
    //
    // Under --certified, we use a tiered strategy:
    //   s ≤ 3: direct red card clauses are RUP from ban clauses (K_s ban width 3
    //          becomes unit after star-edge assumptions). Emit as DRAT additions.
    //          Blue cards: RUP only when t ≤ 3 (symmetric argument).
    //   s ≥ 4: direct red cards are SR with vertex transposition witnesses.
    //          Verify via dsr-trim. Blue cards: skip (the red bound + satsuma
    //          SBP provides sufficient BCP power).
    //
    // Non-certified mode: use Sinz sequential counter (more BCP power from
    // shorter clauses, but Type 4 clauses aren't derivable in DRAT).
    if !no_card {
        if let Some(n) = cardinality::detect_ramsey_n(cnf.nvars) {
            let (s, t) = match detect_ramsey_st_from_cnf(&cnf.clauses) {
                Some(st) => st,
                None => (0, 0),
            };
            if s > 0 && t > 0 {
                let r_s_minus_1 = cardinality::ramsey_lookup(s - 1, t);
                let r_t_minus_1 = cardinality::ramsey_lookup(s, t - 1);
                if r_s_minus_1 > 0 && r_t_minus_1 > 0 {
                    let max_red = (r_s_minus_1 - 1).min(n - 1);
                    let max_blue = (r_t_minus_1 - 1).min(n - 1);
                    println!(
                        "c [card] R({},{}) n={}: red_deg<={} blue_deg<={}",
                        s, t, n, max_red, max_blue
                    );

                    if certified {
                        // Certified mode: use direct card clauses (verifiable).
                        //
                        // Red direct cards are RUP from ban clauses when s ≤ 3:
                        //   Assuming (max_red+1) = R(s-1,t) star edges red, each
                        //   K_s ban (width C(s,2)=3) becomes unit → forces inter-
                        //   edges blue → K_t blue ban fires. BCP closes.
                        //
                        // For s ≥ 4, K_s ban width ≥ 6 → BCP can't close. No
                        // known polynomial DRAT/DSR derivation. Skip card.
                        //
                        // Blue direct cards: RUP only when t ≤ 3 (symmetric).
                        if s > 3 && t > 3 {
                            println!("c [card] s={},t={} > 3: no certified card derivation, skipping", s, t);
                        } else if s <= 3 || t <= 3 {
                            // Estimate direct clause count to avoid combinatorial explosion
                            let est_red = if s <= 3 { estimate_combinations(n - 1, max_red + 1) * n as u64 } else { 0 };
                            let est_blue = if t <= 3 { estimate_combinations(n - 1, max_blue + 1) * n as u64 } else { 0 };
                            let est_total = est_red + est_blue;
                            if est_total > 100_000 {
                                println!(
                                    "c [card] ~{} direct clauses exceeds certified threshold, skipping",
                                    est_total
                                );
                            } else {
                            let red_direct = if s <= 3 {
                                cardinality::direct_red_card_clauses(n, max_red)
                            } else {
                                Vec::new()
                            };
                            let blue_direct = if t <= 3 {
                                cardinality::direct_blue_card_clauses(n, max_blue)
                            } else {
                                Vec::new()
                            };

                            let all_direct: Vec<Vec<cascade::types::Lit>> = red_direct
                                .into_iter()
                                .chain(blue_direct.into_iter())
                                .collect();

                            if !all_direct.is_empty() {
                                card_clauses = all_direct.clone();
                                let new_aug = scratch_path(&input, "_card.cnf");
                                if let Err(e) = append_clauses_as_new_cnf(
                                    &effective_cnf,
                                    &new_aug,
                                    &all_direct,
                                    0,
                                ) {
                                    eprintln!("c [card] write error: {}", e);
                                } else {
                                    let red_mode = if s <= 3 { "RUP" } else { "skip" };
                                    let blue_mode = if t <= 3 { "RUP" } else { "skip" };
                                    println!(
                                        "c [card] {} direct clauses (red {}, blue {})",
                                        all_direct.len(), red_mode, blue_mode
                                    );
                                    effective_cnf = new_aug;
                                }
                            }
                            } // est_total threshold
                        } // s<=3 || t<=3
                    } else {
                        // Non-certified: Sinz counter (more BCP power from shorter clauses)
                        let header = read_cnf_header(&effective_cnf).unwrap_or((cnf.nvars, 0));
                        let top_var = header.0;

                        let (clauses, aux_added, _new_top) =
                            cardinality::ramsey_card_cnf(n, max_red, max_blue, top_var);

                        if !clauses.is_empty() {
                            let new_aug = scratch_path(&input, "_card.cnf");
                            if let Err(e) = append_clauses_as_new_cnf(
                                &effective_cnf,
                                &new_aug,
                                &clauses,
                                aux_added,
                            ) {
                                eprintln!("c [card] write error: {}", e);
                            } else {
                                println!(
                                    "c [card] {} clauses, {} aux vars (sequential counter)",
                                    clauses.len(),
                                    aux_added
                                );
                                effective_cnf = new_aug;
                            }
                        }
                    }
                } else {
                    println!("c [card] R({},{}): unknown bounds, skipping", s, t);
                }
            }
        }
    }

    // === Stage 2: BCP Cascade — try to solve via pure unit propagation ===
    let mut bcp_trail: Vec<cascade::types::Lit> = Vec::new();
    if !no_bcp {
        let bcp_start = Instant::now();
        let augmented_cnf = match dimacs::parse_file(&effective_cnf) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("c [bcp] could not re-parse augmented CNF: {}", e);
                return ExitCode::from(1);
            }
        };
        let bcp_elapsed = bcp_start.elapsed().as_secs_f64();
        let parse_msg = format!(
            "c [bcp] parsed {} vars, {} clauses ({:.3}s)",
            augmented_cnf.nvars, augmented_cnf.clauses.len(), bcp_elapsed
        );
        println!("{}", parse_msg);

        let bcp_solve_start = Instant::now();
        let bcp_result = bcp_cascade(&augmented_cnf);
        let bcp_solve_elapsed = bcp_solve_start.elapsed().as_secs_f64();

        match &bcp_result {
            BcpResult::Unsat { trail, conflicting_clause } => {
                println!(
                    "c [bcp] UNSAT after {} propagations (conflict at clause {}, {:.3}s)",
                    trail.len(),
                    conflicting_clause,
                    bcp_solve_elapsed
                );
                if let Some(p) = &proof {
                    if let Err(e) = std::fs::write(p, "0\n") {
                        eprintln!("c [bcp] proof write error: {}", e);
                    } else {
                        println!("c [bcp] body proof: {} (empty clause)", p.display());
                    }
                }
                if certified {
                    if let Some(p) = &proof {
                        if !card_clauses.is_empty() {
                            let combined = scratch_path(&input, "_combined.drat");
                            print!("c [certify] combining card+body proof... ");
                            if let Err(e) = certify::combine_card_and_body_proof(
                                &card_clauses, &[], p, &combined,
                            ) {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                            println!("ok");
                            print!("c [certify] drat-trim card+body vs pre-card CNF... ");
                            match certify::verify_drat_trim(&pre_card_cnf, &combined) {
                                Ok(()) => println!("VERIFIED"),
                                Err(e) => {
                                    println!("FAILED: {}", e);
                                    eprintln!("c [certify] FATAL: combined proof rejected");
                                    return ExitCode::from(30);
                                }
                            }
                        } else {
                            print!("c [certify] drat-trim body... ");
                            match certify::verify_drat_trim(&effective_cnf, p) {
                                Ok(()) => println!("VERIFIED"),
                                Err(e) => {
                                    println!("FAILED: {}", e);
                                    eprintln!("c [certify] FATAL: body proof rejected");
                                    return ExitCode::from(30);
                                }
                            }
                        }
                    }
                }
                println!("s UNSATISFIABLE");
                return ExitCode::from(20);
            }
            BcpResult::Sat { model } => {
                println!(
                    "c [bcp] SAT — full assignment from BCP ({:.3}s)",
                    bcp_solve_elapsed
                );
                if certified {
                    print!("c [certify] model vs original CNF... ");
                    match certify::verify_model(&cnf, model) {
                        Ok(()) => println!("VERIFIED"),
                        Err(e) => {
                            println!("FAILED: {}", e);
                            eprintln!("c [certify] FATAL: model invalid on original CNF");
                            return ExitCode::from(30);
                        }
                    }
                }
                println!("s SATISFIABLE");
                let mut col = 2;
                print!("v");
                for &lit in model {
                    let s = format!(" {}", lit.raw());
                    if col + s.len() > 78 {
                        println!();
                        print!("v");
                        col = 1;
                    }
                    print!("{}", s);
                    col += s.len();
                }
                println!(" 0");
                return ExitCode::from(10);
            }
            BcpResult::Unresolved { trail, n_assigned, n_unassigned } => {
                println!(
                    "c [bcp] unresolved: {} assigned / {} unassigned ({:.3}s) → falling through to CDCL",
                    n_assigned, n_unassigned, bcp_solve_elapsed
                );
                if !trail.is_empty() {
                    println!("c [bcp] {} trail units available for CDCL warmstart + proof", trail.len());
                    bcp_trail = trail.clone();
                    // Append BCP-derived units to the CNF that CaDiCaL will solve
                    let bcp_aug = scratch_path(&input, "_bcp.cnf");
                    let unit_clauses: Vec<Vec<cascade::types::Lit>> =
                        trail.iter().map(|&l| vec![l]).collect();
                    if let Err(e) = append_clauses_as_new_cnf(
                        &effective_cnf, &bcp_aug, &unit_clauses, 0,
                    ) {
                        eprintln!("c [bcp] warmstart write error: {}", e);
                    } else {
                        println!("c [bcp] wrote {} units to warmstart CNF", trail.len());
                        effective_cnf = bcp_aug;
                    }
                }
            }
        }
    }

    if no_solve {
        println!("c --no-solve: skipping backend invocation");
        return ExitCode::SUCCESS;
    }

    // === Stage 4: CDCL backend (CaDiCaL subprocess) ===
    let backend = CaDiCaL::new();
    let format = if proof.is_some() {
        BackendProofFormat::Drat
    } else {
        BackendProofFormat::None
    };
    let result = match backend.solve(&effective_cnf, proof.as_deref(), format, timeout) {
        Ok(r) => r,
        Err(e) => {
            eprintln!("c backend error: {}", e);
            return ExitCode::from(1);
        }
    };

    println!(
        "c backend={} elapsed={:.2}s conflicts={}",
        backend.name(),
        result.elapsed_secs,
        result.conflicts
    );

    match result.verdict {
        Verdict::Sat => {
            if certified {
                if let Some(model) = &result.model {
                    print!("c [certify] model vs original CNF... ");
                    let lits: Vec<cascade::types::Lit> =
                        model.iter().map(|&v| cascade::types::Lit::new(v)).collect();
                    match certify::verify_model(&cnf, &lits) {
                        Ok(()) => println!("VERIFIED"),
                        Err(e) => {
                            println!("FAILED: {}", e);
                            eprintln!("c [certify] FATAL: model invalid on original CNF");
                            return ExitCode::from(30);
                        }
                    }
                }
            }
            println!("s SATISFIABLE");
            if let Some(model) = &result.model {
                let mut col = 2;
                print!("v");
                for &lit in model {
                    let s = format!(" {}", lit);
                    if col + s.len() > 78 {
                        println!();
                        print!("v");
                        col = 1;
                    }
                    print!("{}", s);
                    col += s.len();
                }
                println!(" 0");
            }
            ExitCode::from(10)
        }
        Verdict::Unsat => {
            if let Some(p) = &result.proof_path {
                println!("c body proof: {}", p.display());
                if certified {
                    if !card_clauses.is_empty() || !bcp_trail.is_empty() {
                        let combined = scratch_path(&input, "_combined.drat");
                        print!("c [certify] combining card({})+bcp({})+body proof... ",
                            card_clauses.len(), bcp_trail.len());
                        if let Err(e) = certify::combine_card_and_body_proof(
                            &card_clauses, &bcp_trail, p, &combined,
                        ) {
                            println!("FAILED: {}", e);
                            return ExitCode::from(30);
                        }
                        println!("ok");
                        print!("c [certify] drat-trim combined vs pre-card CNF... ");
                        match certify::verify_drat_trim(&pre_card_cnf, &combined) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                eprintln!("c [certify] FATAL: combined proof rejected");
                                return ExitCode::from(30);
                            }
                        }
                    } else {
                        print!("c [certify] drat-trim body... ");
                        match certify::verify_drat_trim(&effective_cnf, p) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                eprintln!("c [certify] FATAL: body proof rejected");
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
            }
            println!("s UNSATISFIABLE");
            ExitCode::from(20)
        }
        Verdict::Unknown => {
            println!("s UNKNOWN");
            ExitCode::SUCCESS
        }
    }
}

/// Estimate C(n, k) — binomial coefficient. Returns u64::MAX on overflow.
fn estimate_combinations(n: u32, k: u32) -> u64 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k) as u64;
    let n = n as u64;
    let mut result: u64 = 1;
    for i in 0..k {
        result = result.saturating_mul(n - i) / (i + 1);
    }
    result
}

fn scratch_path(input: &Path, suffix: &str) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cascade");
    let mut p = std::env::temp_dir();
    p.push(format!("{}{}", stem, suffix));
    p
}

/// Read just the `p cnf nvars nclauses` header from a CNF file.
fn read_cnf_header(path: &Path) -> Option<(u32, u32)> {
    let f = std::fs::File::open(path).ok()?;
    let r = BufReader::new(f);
    for line in r.lines().flatten() {
        let s = line.trim();
        if let Some(rest) = s.strip_prefix("p cnf") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() >= 2 {
                return Some((parts[0].parse().ok()?, parts[1].parse().ok()?));
            }
        }
    }
    None
}

/// Detect (s, t) for R(s, t) from the smallest all-negative and all-positive
/// clause widths in the bare CNF.
fn detect_ramsey_st_from_cnf(clauses: &[cascade::types::Clause]) -> Option<(u32, u32)> {
    let mut min_neg = u32::MAX;
    let mut min_pos = u32::MAX;
    for c in clauses {
        let lits = c.lits();
        if lits.is_empty() {
            continue;
        }
        let all_neg = lits.iter().all(|l| l.is_negative());
        let all_pos = lits.iter().all(|l| l.is_positive());
        if all_neg {
            min_neg = min_neg.min(lits.len() as u32);
        }
        if all_pos {
            min_pos = min_pos.min(lits.len() as u32);
        }
    }
    if min_neg == u32::MAX || min_pos == u32::MAX {
        return None;
    }
    cardinality::detect_ramsey_st(min_neg, min_pos)
}

/// Read a CNF file and write a new CNF that appends the given extra clauses.
/// Updates the `p cnf` header with the new variable and clause counts.
fn append_clauses_as_new_cnf(
    src: &Path,
    dst: &Path,
    extra_clauses: &[Vec<cascade::types::Lit>],
    extra_aux_vars: u32,
) -> std::io::Result<()> {
    let (old_nvars, old_nclauses) = read_cnf_header(src)
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "no p cnf header"))?;
    let new_nvars = old_nvars + extra_aux_vars;
    let new_nclauses = old_nclauses + extra_clauses.len() as u32;

    let in_f = std::fs::File::open(src)?;
    let out_f = std::fs::File::create(dst)?;
    let mut out = std::io::BufWriter::new(out_f);
    writeln!(out, "p cnf {} {}", new_nvars, new_nclauses)?;
    let r = BufReader::new(in_f);
    for line in r.lines() {
        let line = line?;
        let s = line.trim_start();
        if s.is_empty() || s.starts_with('c') || s.starts_with("p ") {
            continue;
        }
        writeln!(out, "{}", line)?;
    }
    for cl in extra_clauses {
        for l in cl {
            write!(out, "{} ", l.raw())?;
        }
        writeln!(out, "0")?;
    }
    out.flush()?;
    Ok(())
}
