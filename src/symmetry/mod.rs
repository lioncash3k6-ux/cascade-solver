//! Symmetry detection + symmetry-breaking predicate (SBP) generation.
//!
//! A `SymmetryBreaker` takes a CNF and produces two artifacts:
//!   1. An augmented CNF (original + SBP clauses)
//!   2. A proof that the augmented CNF is equisatisfiable with the original
//!
//! The first concrete implementation is satsuma (Markus Anders et al., TACAS
//! 2026), which uses the dejavu algorithm for symmetry detection and
//! orbitopal fixing for SBP generation.

use std::path::{Path, PathBuf};

pub mod satsuma;

#[derive(Debug)]
pub struct BreakResult {
    /// Path to the augmented CNF file (original + SBP clauses).
    pub augmented_cnf: PathBuf,
    /// Path to the equisatisfiability proof (VeriPB or DSR), if produced.
    pub equisat_proof: Option<PathBuf>,
    /// Number of generators detected in the symmetry group.
    pub n_generators: u32,
    /// Number of SBP clauses added.
    pub n_sbp_clauses: u32,
    /// Number of auxiliary variables added.
    pub n_aux_vars: u32,
    /// Wall-clock time spent in the breaker.
    pub elapsed_secs: f64,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum EquisatProofFormat {
    /// No proof — just the augmented CNF.
    None,
    /// VeriPB pseudo-Boolean proof (used by satsuma).
    VeriPb,
    /// DSR substitution-redundancy proof.
    Dsr,
}

pub trait SymmetryBreaker {
    fn name(&self) -> &str;

    /// Detect symmetries and produce an augmented CNF (with SBP) plus the
    /// equisatisfiability proof (if requested).
    fn break_symmetries(
        &self,
        cnf_path: &Path,
        out_aug: &Path,
        out_proof: Option<&Path>,
        format: EquisatProofFormat,
    ) -> std::io::Result<BreakResult>;
}
