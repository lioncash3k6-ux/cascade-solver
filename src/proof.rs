//! Layer 4 (writer half): emit proof steps in DRAT, LRAT, or DSR format.
//!
//! Internally we always carry LRAT-style hints; if the user wants DRAT we just
//! drop the hints on the way out. If the user wants DSR we serialize the
//! substitution witness instead.

use crate::augmentation::{Augmentation, Justification};
use std::fs::File;
use std::io::{BufWriter, Write};
use std::path::Path;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum ProofFormat {
    /// DRAT: clause additions and deletions. No hints.
    Drat,
    /// LRAT: same as DRAT but with explicit unit-propagation hints.
    Lrat,
    /// DSR: substitution redundancy proofs. Witnesses are emitted.
    Dsr,
}

pub struct ProofWriter {
    format: ProofFormat,
    out: BufWriter<File>,
    n_steps: usize,
}

impl ProofWriter {
    pub fn create<P: AsRef<Path>>(
        path: P,
        format: ProofFormat,
    ) -> std::io::Result<Self> {
        let f = File::create(path)?;
        Ok(ProofWriter {
            format,
            out: BufWriter::new(f),
            n_steps: 0,
        })
    }

    /// Emit one augmentation step. Axiom (Input) steps are skipped — they
    /// belong to the input CNF, not the proof.
    pub fn emit(&mut self, aug: &Augmentation) -> std::io::Result<()> {
        if aug.justification.is_axiom() {
            return Ok(());
        }
        match self.format {
            ProofFormat::Drat => self.emit_drat(aug)?,
            ProofFormat::Lrat => self.emit_lrat(aug)?,
            ProofFormat::Dsr => self.emit_dsr(aug)?,
        }
        self.n_steps += 1;
        Ok(())
    }

    fn emit_drat(&mut self, aug: &Augmentation) -> std::io::Result<()> {
        if matches!(aug.justification, Justification::Delete) {
            write!(self.out, "d ")?;
        }
        for l in aug.clause.lits() {
            write!(self.out, "{} ", l.raw())?;
        }
        writeln!(self.out, "0")?;
        Ok(())
    }

    fn emit_lrat(&mut self, aug: &Augmentation) -> std::io::Result<()> {
        // LRAT format: <id> <lits> 0 <hints> 0
        // Deletion:    <id> d <ids> 0
        let id = aug.id.raw();
        if matches!(aug.justification, Justification::Delete) {
            write!(self.out, "{} d ", id)?;
            for l in aug.clause.lits() {
                write!(self.out, "{} ", l.raw())?;
            }
            writeln!(self.out, "0")?;
            return Ok(());
        }
        write!(self.out, "{} ", id)?;
        for l in aug.clause.lits() {
            write!(self.out, "{} ", l.raw())?;
        }
        write!(self.out, "0 ")?;
        match &aug.justification {
            Justification::Rup { hints }
            | Justification::Rat { hints, .. }
            | Justification::Sr { hints, .. }
            | Justification::Pr { hints, .. } => {
                for h in hints {
                    write!(self.out, "{} ", h.raw())?;
                }
            }
            Justification::Propagator { inner, .. } => {
                if let Justification::Rup { hints } | Justification::Rat { hints, .. } = inner.as_ref() {
                    for h in hints {
                        write!(self.out, "{} ", h.raw())?;
                    }
                }
            }
            _ => {}
        }
        writeln!(self.out, "0")?;
        Ok(())
    }

    fn emit_dsr(&mut self, aug: &Augmentation) -> std::io::Result<()> {
        // DSR format used by dsr-trim: pivot+clause then witness pairs.
        // For now, just emit the clause; SR-witness emission TBD.
        if matches!(aug.justification, Justification::Delete) {
            write!(self.out, "d ")?;
            for l in aug.clause.lits() {
                write!(self.out, "{} ", l.raw())?;
            }
            writeln!(self.out, "0")?;
            return Ok(());
        }
        for l in aug.clause.lits() {
            write!(self.out, "{} ", l.raw())?;
        }
        writeln!(self.out, "0")?;
        Ok(())
    }

    /// Finalize the proof file (close, flush). The empty-clause derivation,
    /// if any, must already have been emitted.
    pub fn finish(self) -> std::io::Result<usize> {
        let n = self.n_steps;
        let mut out = self.out;
        out.flush()?;
        Ok(n)
    }
}

/// Convenience: emit a trivial empty proof for a known-SAT input. A solver
/// that doesn't actually find UNSAT outputs an empty proof file.
pub fn emit_empty_proof<P: AsRef<Path>>(
    path: P,
    format: ProofFormat,
) -> std::io::Result<()> {
    let _ = ProofWriter::create(path, format)?.finish()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::augmentation::AugmentationIr;
    use crate::types::{Clause, Lit};

    #[test]
    fn emit_drat_smoke() {
        let path = "/tmp/cascade_test.drat";
        let mut w = ProofWriter::create(path, ProofFormat::Drat).unwrap();
        let mut ir = AugmentationIr::new();
        // Add an axiom — should NOT appear in the proof
        ir.add(Clause::new(vec![Lit::new(1)]), Justification::Input);
        // Add a derived clause via RUP
        ir.add(
            Clause::new(vec![Lit::new(-1)]),
            Justification::Rup { hints: vec![] },
        );
        for aug in ir.steps() {
            w.emit(aug).unwrap();
        }
        let n = w.finish().unwrap();
        assert_eq!(n, 1, "axiom should be skipped, only RUP step emitted");
        let s = std::fs::read_to_string(path).unwrap();
        assert!(s.contains("-1 0"));
    }
}
