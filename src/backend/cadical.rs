//! CaDiCaL backend (subprocess invocation).
//!
//! Spawns the system `cadical` binary, optionally requesting a DRAT or LRAT
//! proof file. Parses stdout for the verdict line (`s SATISFIABLE` /
//! `s UNSATISFIABLE` / `s UNKNOWN`) and the model lines (`v ...`).
//!
//! Exit codes: 10 = SAT, 20 = UNSAT, anything else = unknown/error.
//! Wall-clock timeout enforced via the `timeout` shell utility.

use super::{Backend, BackendProofFormat, SolveResult, Verdict};
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

pub struct CaDiCaL {
    pub binary: PathBuf,
}

impl CaDiCaL {
    pub fn new() -> Self {
        CaDiCaL {
            binary: PathBuf::from("cadical"),
        }
    }

    pub fn with_binary<P: Into<PathBuf>>(binary: P) -> Self {
        CaDiCaL {
            binary: binary.into(),
        }
    }
}

impl Default for CaDiCaL {
    fn default() -> Self {
        Self::new()
    }
}

impl Backend for CaDiCaL {
    fn name(&self) -> &str {
        "cadical"
    }

    fn solve(
        &self,
        cnf_path: &Path,
        proof_path: Option<&Path>,
        format: BackendProofFormat,
        timeout_secs: Option<u32>,
    ) -> std::io::Result<SolveResult> {
        let mut cmd = if let Some(t) = timeout_secs {
            let mut c = Command::new("timeout");
            c.arg(format!("{}", t)).arg(&self.binary);
            c
        } else {
            Command::new(&self.binary)
        };

        // CaDiCaL flags for proof format selection.
        match format {
            BackendProofFormat::None => {}
            BackendProofFormat::Drat => {} // default
            BackendProofFormat::Lrat => {
                cmd.arg("--lrat=1");
            }
        }

        cmd.arg(cnf_path);
        if let Some(pp) = proof_path {
            if format != BackendProofFormat::None {
                cmd.arg(pp);
            }
        }

        let start = Instant::now();
        let output = cmd.output()?;
        let elapsed = start.elapsed().as_secs_f64();

        let exit_code = output.status.code().unwrap_or(-1);
        let stdout = String::from_utf8_lossy(&output.stdout);

        let verdict = match exit_code {
            10 => Verdict::Sat,
            20 => Verdict::Unsat,
            _ => Verdict::Unknown,
        };

        let mut model: Option<Vec<i32>> = None;
        let mut conflicts: u64 = 0;

        if verdict == Verdict::Sat {
            let mut m: Vec<i32> = Vec::new();
            for line in stdout.lines() {
                if let Some(rest) = line.strip_prefix("v ") {
                    for tok in rest.split_whitespace() {
                        if let Ok(n) = tok.parse::<i32>() {
                            if n != 0 {
                                m.push(n);
                            }
                        }
                    }
                }
            }
            if !m.is_empty() {
                model = Some(m);
            }
        }

        for line in stdout.lines() {
            if let Some(rest) = line.trim_start().strip_prefix("c conflicts:") {
                let s = rest.trim();
                if let Some(num_end) = s.find(|c: char| !c.is_ascii_digit()) {
                    if let Ok(n) = s[..num_end].parse::<u64>() {
                        conflicts = n;
                        break;
                    }
                } else if let Ok(n) = s.parse::<u64>() {
                    conflicts = n;
                    break;
                }
            }
        }

        let proof_path = match (proof_path, format) {
            (Some(p), BackendProofFormat::Drat) | (Some(p), BackendProofFormat::Lrat)
                if verdict == Verdict::Unsat =>
            {
                Some(p.to_path_buf())
            }
            _ => None,
        };

        Ok(SolveResult {
            verdict,
            proof_path,
            model,
            conflicts,
            elapsed_secs: elapsed,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io::Write;

    fn write_tmp(name: &str, contents: &str) -> PathBuf {
        let mut p = std::env::temp_dir();
        p.push(name);
        let mut f = std::fs::File::create(&p).unwrap();
        f.write_all(contents.as_bytes()).unwrap();
        p
    }

    #[test]
    fn cadical_trivial_sat() {
        let cnf = write_tmp("cascade_trivial_sat.cnf", "p cnf 2 1\n1 2 0\n");
        let backend = CaDiCaL::new();
        let r = backend
            .solve(&cnf, None, BackendProofFormat::None, Some(10))
            .unwrap();
        assert_eq!(r.verdict, Verdict::Sat);
        assert!(r.model.is_some());
    }

    #[test]
    fn cadical_trivial_unsat() {
        let cnf = write_tmp(
            "cascade_trivial_unsat.cnf",
            "p cnf 1 2\n1 0\n-1 0\n",
        );
        let mut proof = std::env::temp_dir();
        proof.push("cascade_trivial_unsat.drat");
        let backend = CaDiCaL::new();
        let r = backend
            .solve(
                &cnf,
                Some(&proof),
                BackendProofFormat::Drat,
                Some(10),
            )
            .unwrap();
        assert_eq!(r.verdict, Verdict::Unsat);
        assert!(r.proof_path.is_some());
    }
}
