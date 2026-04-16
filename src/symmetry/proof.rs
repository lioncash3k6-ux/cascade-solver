//! VeriPB proof emission for the online symmetry propagator (PR-5).
//!
//! Every blocking clause or propagation reason emitted by the
//! [`SymmetryPropagator`](super::online::SymmetryPropagator) is
//! logged here along with the responsible generator index. At the end
//! of the solve we serialize the log as a sequence of VeriPB `red`
//! substitution-redundancy steps, each naming the generator as its
//! witness.
//!
//! # Composition
//!
//! The final VeriPB proof fed to `veripb` is composed by
//! [`build_veripb_proof`]:
//!   1. Satsuma's VeriPB proof provides the `def_order`/`load_order`
//!      preamble (the lex ordering against which `red` witnesses are
//!      checked). We truncate satsuma's proof right after its
//!      `load_order …;` line, dropping satsuma's own SBP `dom` steps
//!      since under `--online-sym` those SBP clauses are not in the
//!      CNF.
//!   2. Our `red` steps are appended, one per logged clause.
//!   3. The proof is closed with `output NONE; conclusion NONE; end
//!      pseudo-Boolean proof;`.
//!
//! The augmented CNF fed to `drat-trim` includes every clause we
//! logged (see [`SymProofLog::write_clauses_cnf`]), plus the bare CNF,
//! card additions, chain, and BCP trail.

use crate::symmetry::generators::Permutation;
use std::fs::File;
use std::io::{self, BufRead, BufReader, Write};
use std::path::Path;

/// One entry in the proof log: the emitted clause plus the generator
/// that justifies it.
#[derive(Clone, Debug)]
pub struct LoggedClause {
    pub clause: Vec<i32>,
    pub gen_idx: usize,
}

/// Accumulator for [`LoggedClause`] entries. Cheaply cloneable and
/// `Send` so the propagator can own one even inside a `Box<dyn>`.
#[derive(Clone, Debug, Default)]
pub struct SymProofLog {
    pub entries: Vec<LoggedClause>,
}

impl SymProofLog {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn push(&mut self, clause: Vec<i32>, gen_idx: usize) {
        // Dedup consecutive identical emissions — they can happen when
        // CaDiCaL re-queries the propagator after backjump.
        if let Some(last) = self.entries.last() {
            if last.clause == clause && last.gen_idx == gen_idx {
                return;
            }
        }
        self.entries.push(LoggedClause { clause, gen_idx });
    }

    pub fn len(&self) -> usize { self.entries.len() }
    pub fn is_empty(&self) -> bool { self.entries.is_empty() }

    /// Serialize every logged clause as DIMACS to `path` (appended to
    /// the CNF the drat-trim step will consume).
    pub fn write_clauses_cnf(&self, path: &Path) -> io::Result<()> {
        let mut out = File::create(path)?;
        for entry in &self.entries {
            for l in &entry.clause {
                write!(out, "{} ", l)?;
            }
            writeln!(out, "0")?;
        }
        out.flush()
    }
}

/// Serialize a clause as `1 lit1 1 lit2 … >= 1`.
fn fmt_clause_pb(clause: &[i32]) -> String {
    let mut s = String::new();
    for &l in clause {
        if l > 0 {
            s.push_str(&format!("1 x{} ", l));
        } else {
            s.push_str(&format!("1 ~x{} ", -l));
        }
    }
    s.push_str(">= 1");
    s
}

/// Serialize a permutation as a VeriPB substitution witness.
///
/// Example: `x1 -> x5 x2 -> ~x2 x3 -> x1`.
fn fmt_permutation(gen: &Permutation) -> String {
    let mut s = String::new();
    let mut first = true;
    for v in 1..=gen.n_vars() {
        let img = gen.apply_var(v);
        if img == v as i32 {
            continue; // fixed point — omit
        }
        if !first {
            s.push(' ');
        }
        first = false;
        if img > 0 {
            s.push_str(&format!("x{} -> x{}", v, img));
        } else {
            s.push_str(&format!("x{} -> ~x{}", v, -img));
        }
    }
    s
}

/// Truncate satsuma's VeriPB proof after the `load_order …;` line.
/// Returns the preamble text (including the trailing newline after
/// `load_order`).
fn extract_satsuma_preamble(proof_path: &Path) -> io::Result<String> {
    let f = File::open(proof_path)?;
    let reader = BufReader::new(f);
    let mut preamble = String::new();
    for line in reader.lines() {
        let line = line?;
        preamble.push_str(&line);
        preamble.push('\n');
        // The preamble ends at the first `load_order` line (which
        // introduces the ordering). After it, satsuma emits its own
        // `dom …` SBP steps, which we discard.
        if line.trim_start().starts_with("load_order ")
            && line.trim_end().ends_with(';')
            && !line.trim_start().starts_with("load_order;")
        {
            return Ok(preamble);
        }
    }
    // If we never saw `load_order`, return what we have and let VeriPB
    // complain downstream.
    Ok(preamble)
}

/// Compose the final VeriPB proof for `--online-sym --certified`.
///
/// * `satsuma_proof` — the proof file satsuma emitted (used for its
///   `def_order`/`load_order` preamble only).
/// * `generators` — the generator set we used (indexed by `gen_idx`).
/// * `log` — the clauses we want to justify.
/// * `out` — the composite VeriPB file to write.
pub fn build_veripb_proof(
    satsuma_proof: &Path,
    generators: &[Permutation],
    log: &SymProofLog,
    out: &Path,
) -> io::Result<()> {
    let preamble = extract_satsuma_preamble(satsuma_proof)?;

    let f = File::create(out)?;
    let mut w = std::io::BufWriter::new(f);
    w.write_all(preamble.as_bytes())?;

    for entry in &log.entries {
        let gen = &generators[entry.gen_idx];
        let pb = fmt_clause_pb(&entry.clause);
        let subst = fmt_permutation(gen);
        // VeriPB red syntax: `red <pb_clause> : <substitution> ;`
        // (colon before witness, semicolon terminator).
        writeln!(w, "red {} : {} ;", pb, subst)?;
    }

    writeln!(w)?;
    writeln!(w, "output NONE;")?;
    writeln!(w, "conclusion NONE;")?;
    writeln!(w, "end pseudo-Boolean proof;")?;
    w.flush()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symmetry::generators::Permutation;

    #[test]
    fn fmt_clause_pb_basic() {
        assert_eq!(fmt_clause_pb(&[1, -2, 3]), "1 x1 1 ~x2 1 x3 >= 1");
    }

    #[test]
    fn fmt_permutation_skips_fixed_points() {
        // Identity on 1, swap(2,3), polarity-flip on 4.
        let p = Permutation::from_mapping(4, &[(2, 3), (3, 2), (4, -4)]);
        assert_eq!(fmt_permutation(&p), "x2 -> x3 x3 -> x2 x4 -> ~x4");
    }

    #[test]
    fn log_dedups_consecutive_identical() {
        let mut log = SymProofLog::new();
        log.push(vec![-1, 2], 0);
        log.push(vec![-1, 2], 0);
        log.push(vec![-1, 3], 0);
        assert_eq!(log.len(), 2);
    }

    #[test]
    fn log_keeps_distinct_entries() {
        let mut log = SymProofLog::new();
        log.push(vec![-1, 2], 0);
        log.push(vec![-1, 2], 1); // different gen
        log.push(vec![-2, 3], 0); // different clause
        assert_eq!(log.len(), 3);
    }

    #[test]
    fn write_clauses_cnf_emits_dimacs() {
        let mut log = SymProofLog::new();
        log.push(vec![-1, 2], 0);
        log.push(vec![3, 4, -5], 1);
        let mut path = std::env::temp_dir();
        path.push("cascade_sym_proof_test.cnf");
        log.write_clauses_cnf(&path).unwrap();
        let content = std::fs::read_to_string(&path).unwrap();
        assert_eq!(content, "-1 2 0\n3 4 -5 0\n");
    }
}
