//! Satsuma symmetry breaker (subprocess wrapper).
//!
//! Invokes `/root/satsuma/satsuma` (or a configurable path) to detect
//! symmetries and generate symmetry-breaking predicates. Produces a
//! VeriPB equisatisfiability proof against the bare CNF.
//!
//! The satsuma proof file lacks the closing `output NONE; conclusion NONE;
//! end pseudo-Boolean proof;` lines — we append them after the subprocess
//! returns so `veripb` will accept the file.

use super::generators::{parse_veripb_proof, GeneratorSet};
use super::{BreakResult, EquisatProofFormat, SymmetryBreaker};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Instant;

pub struct Satsuma {
    pub binary: PathBuf,
}

impl Satsuma {
    pub fn new() -> Self {
        Satsuma {
            binary: PathBuf::from("/root/satsuma/satsuma"),
        }
    }

    pub fn with_binary<P: Into<PathBuf>>(binary: P) -> Self {
        Satsuma {
            binary: binary.into(),
        }
    }
}

impl Default for Satsuma {
    fn default() -> Self {
        Self::new()
    }
}

impl Satsuma {
    /// Run satsuma on `cnf_path` and return the detected `GeneratorSet`.
    ///
    /// Internally: invokes satsuma with `--proof-file` pointed at a
    /// scratch location, parses the resulting VeriPB proof for `dom`
    /// lines and the `load_order` declaration. The augmented CNF and
    /// the scratch proof file are left on disk at `scratch_dir` for
    /// the caller to reuse (e.g., feeding the augmented CNF to CaDiCaL
    /// in hybrid mode, or composing the proof).
    ///
    /// `n_vars` is the number of variables in the **original** CNF (not
    /// including satsuma's auxiliary SBP vars). Generators always act
    /// on the original variables; any image referencing an aux var is
    /// filtered out during parsing.
    pub fn extract_generators(
        &self,
        cnf_path: &Path,
        scratch_dir: &Path,
        n_vars: u32,
    ) -> std::io::Result<(GeneratorSet, PathBuf, PathBuf)> {
        std::fs::create_dir_all(scratch_dir)?;
        let stem = cnf_path
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("satsuma");
        let aug_path = scratch_dir.join(format!("{}_aug.cnf", stem));
        let proof_path = scratch_dir.join(format!("{}.veripb", stem));

        let _ = self.break_symmetries(
            cnf_path,
            &aug_path,
            Some(&proof_path),
            EquisatProofFormat::VeriPb,
        )?;

        let gs = parse_veripb_proof(&proof_path, n_vars)?;
        Ok((gs, aug_path, proof_path))
    }
}

impl SymmetryBreaker for Satsuma {
    fn name(&self) -> &str {
        "satsuma"
    }

    fn break_symmetries(
        &self,
        cnf_path: &Path,
        out_aug: &Path,
        out_proof: Option<&Path>,
        format: EquisatProofFormat,
    ) -> std::io::Result<BreakResult> {
        let start = Instant::now();
        let mut cmd = Command::new(&self.binary);
        cmd.arg("--file").arg(cnf_path);
        cmd.arg("--out-file").arg(out_aug);

        let proof_requested = matches!(
            (out_proof, format),
            (Some(_), EquisatProofFormat::VeriPb)
        );
        if proof_requested {
            if let Some(p) = out_proof {
                cmd.arg("--proof-file").arg(p);
            }
        }

        let output = cmd.output()?;
        let elapsed = start.elapsed().as_secs_f64();
        let stderr = String::from_utf8_lossy(&output.stderr);

        if !output.status.success() {
            return Err(std::io::Error::new(
                std::io::ErrorKind::Other,
                format!(
                    "satsuma exited with status {:?}: {}",
                    output.status, stderr
                ),
            ));
        }

        // Parse stats from satsuma's stderr.
        // Looking for lines like:
        //   c    [group: #gens 24 #avg_support 92.00]
        //   c    [sbp: #clauses 3264 #add_vars 1080]
        let mut n_generators = 0u32;
        let mut n_sbp_clauses = 0u32;
        let mut n_aux_vars = 0u32;

        for line in stderr.lines() {
            if line.contains("#gens") {
                if let Some(idx) = line.find("#gens ") {
                    let rest = &line[idx + 6..];
                    if let Some(num_end) = rest.find(|c: char| !c.is_ascii_digit()) {
                        if let Ok(n) = rest[..num_end].parse::<u32>() {
                            n_generators = n;
                        }
                    }
                }
            }
            if line.contains("#clauses") && line.contains("sbp") {
                if let Some(idx) = line.find("#clauses ") {
                    let rest = &line[idx + 9..];
                    if let Some(num_end) = rest.find(|c: char| !c.is_ascii_digit()) {
                        if let Ok(n) = rest[..num_end].parse::<u32>() {
                            n_sbp_clauses = n;
                        }
                    }
                }
                if let Some(idx) = line.find("#add_vars ") {
                    let rest = &line[idx + 10..];
                    if let Some(num_end) = rest.find(|c: char| !c.is_ascii_digit()) {
                        if let Ok(n) = rest[..num_end].parse::<u32>() {
                            n_aux_vars = n;
                        }
                    }
                }
            }
        }

        // Append the closing lines to the VeriPB proof so veripb will accept it.
        // Satsuma's `--proof-file` output is missing the trailing
        //   output NONE;
        //   conclusion NONE;
        //   end pseudo-Boolean proof;
        if proof_requested {
            if let Some(p) = out_proof {
                let mut f = OpenOptions::new().append(true).open(p)?;
                writeln!(f)?;
                writeln!(f, "output NONE;")?;
                writeln!(f, "conclusion NONE;")?;
                writeln!(f, "end pseudo-Boolean proof;")?;
            }
        }

        Ok(BreakResult {
            augmented_cnf: out_aug.to_path_buf(),
            equisat_proof: if proof_requested {
                out_proof.map(|p| p.to_path_buf())
            } else {
                None
            },
            n_generators,
            n_sbp_clauses,
            n_aux_vars,
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
    fn satsuma_no_symmetries() {
        // A CNF with no exploitable symmetry — satsuma should still produce
        // an augmented file (possibly with 0 SBP clauses) and not crash.
        let cnf = write_tmp("cascade_satsuma_nosym.cnf", "p cnf 3 2\n1 -2 3 0\n-1 2 0\n");
        let mut aug = std::env::temp_dir();
        aug.push("cascade_satsuma_nosym_aug.cnf");
        let breaker = Satsuma::new();
        let r = breaker
            .break_symmetries(&cnf, &aug, None, EquisatProofFormat::None)
            .unwrap();
        assert!(r.augmented_cnf.exists());
    }
}
