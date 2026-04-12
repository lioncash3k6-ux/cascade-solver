//! Cascade — structural cascade SAT solver.
//!
//! Architecture (4 layers):
//!   1. Constraint IR     — typed first-class constraints
//!   2. Augmentation IR   — sequence of (clause, justification)
//!   3. BCP/Search engine — emits a proof step per state transition
//!   4. Verifier          — embedded checker, every step is incrementally verified
//!
//! Design principle: the solver IS a proof transcript being checked. Bugs become
//! slowdowns, never wrong answers.

pub mod types;
pub mod dimacs;
pub mod constraint;
pub mod augmentation;
pub mod proof;
pub mod backend;
pub mod symmetry;
pub mod cardinality;
pub mod bcp;
pub mod certify;

pub use types::{Lit, Var, ClauseId, Clause};
pub use constraint::Constraint;
pub use augmentation::{Augmentation, Justification};
pub use proof::ProofWriter;
pub use backend::{Backend, BackendProofFormat, SolveResult, Verdict};
pub use symmetry::{BreakResult, EquisatProofFormat, SymmetryBreaker};
