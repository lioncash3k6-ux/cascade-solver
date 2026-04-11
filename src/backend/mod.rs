//! Backend layer: CDCL solvers wrapped behind a uniform interface.
//!
//! A backend takes a CNF file and produces a `Verdict` plus an optional
//! proof file. The cascade orchestrator calls into a backend after Stage 1+2
//! (structural augmentation + BCP cascade) have failed to settle the problem.
//!
//! The first backend is CaDiCaL invoked as a subprocess. Future backends:
//! kissat, lingeling, in-process CaDiCaL via FFI, etc.

use std::path::{Path, PathBuf};

pub mod cadical;

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum Verdict {
    Sat,
    Unsat,
    Unknown,
}

/// Result of a backend solve. The proof file (DRAT/LRAT) is left on disk
/// for the orchestrator to integrate.
#[derive(Debug)]
pub struct SolveResult {
    pub verdict: Verdict,
    pub proof_path: Option<PathBuf>,
    pub model: Option<Vec<i32>>,
    pub conflicts: u64,
    pub elapsed_secs: f64,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq)]
pub enum BackendProofFormat {
    None,
    Drat,
    Lrat,
}

/// Solver-agnostic backend interface.
pub trait Backend {
    /// Human-readable name for diagnostics.
    fn name(&self) -> &str;

    /// Solve a CNF file. The backend may write a proof file at `proof_path`
    /// (if requested via the format argument).
    fn solve(
        &self,
        cnf_path: &Path,
        proof_path: Option<&Path>,
        format: BackendProofFormat,
        timeout_secs: Option<u32>,
    ) -> std::io::Result<SolveResult>;
}
