//! Layer 1: Constraint IR — typed first-class constraints.
//!
//! At this layer the formula is a set of typed constraints, not just clauses.
//! The lowering pass turns each constraint into a sequence of clauses (Layer 2)
//! with proof-justified augmentations.

use crate::types::{Clause, Lit, Var};

/// A first-class constraint. Each variant has a different lowering strategy.
#[derive(Clone, Debug)]
pub enum Constraint {
    /// A plain CNF clause: at least one literal must be true.
    Clause(Clause),

    /// `lo <= sum(lits) <= hi` (cardinality constraint).
    /// Encoded via sequential counter (Sinz 2005) at lowering time.
    Cardinality {
        lits: Vec<Lit>,
        lo: u32,
        hi: u32,
    },

    /// XOR over a set of literals: their sum mod 2 equals `rhs`.
    /// Encoded via Tseitin XOR gates.
    Xor { lits: Vec<Lit>, rhs: bool },

    /// At-most-one constraint (special case of cardinality, faster encoding).
    AtMostOne(Vec<Lit>),

    /// Symmetry breaking: inject SBP based on a generator set.
    /// Lowering uses the satsuma orbital decomposition.
    Symmetry { generators: Vec<Permutation> },

    /// A definitional extension introducing a fresh variable: `aux <-> def_lits`.
    /// Encoded as Tseitin gates with PR/DSR justification.
    Definition { aux: Var, def: GateDef },
}

/// A permutation of variables, represented as a sparse map of moved indices.
#[derive(Clone, Debug)]
pub struct Permutation {
    /// `pairs[i] = (from, to)` means the permutation maps `from` to `to`.
    /// Variables not in this list are fixed.
    pub pairs: Vec<(Var, Var)>,
}

/// Definition of an auxiliary variable in terms of existing ones.
#[derive(Clone, Debug)]
pub enum GateDef {
    /// `aux <-> AND(lits)`
    And(Vec<Lit>),
    /// `aux <-> OR(lits)`
    Or(Vec<Lit>),
    /// `aux <-> XOR(lits)`
    Xor(Vec<Lit>),
    /// `aux <-> ITE(c, t, e)`  — if c then t else e
    Ite { c: Lit, t: Lit, e: Lit },
}

impl Constraint {
    /// Approximate clause count after lowering. Used for sizing.
    pub fn estimated_clauses(&self) -> usize {
        match self {
            Constraint::Clause(_) => 1,
            Constraint::Cardinality { lits, hi, .. } => {
                let n = lits.len();
                let k = *hi as usize;
                if k >= n { 0 } else { n + 2 * k * (n - 1) }
            }
            Constraint::Xor { lits, .. } => 1usize << lits.len().min(8),
            Constraint::AtMostOne(lits) => {
                let n = lits.len();
                n * (n - 1) / 2  // pairwise; smarter encodings possible
            }
            Constraint::Symmetry { generators } => generators.len() * 4,
            Constraint::Definition { def, .. } => match def {
                GateDef::And(l) | GateDef::Or(l) => l.len() + 1,
                GateDef::Xor(l) => 1usize << l.len().min(8),
                GateDef::Ite { .. } => 4,
            },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cardinality_estimate() {
        let c = Constraint::Cardinality {
            lits: (1..=10).map(|i| Lit::new(i)).collect(),
            lo: 0,
            hi: 3,
        };
        // 10 + 2*3*9 = 64
        assert_eq!(c.estimated_clauses(), 64);
    }

    #[test]
    fn at_most_one_estimate() {
        let c = Constraint::AtMostOne((1..=5).map(|i| Lit::new(i)).collect());
        // 5*4/2 = 10
        assert_eq!(c.estimated_clauses(), 10);
    }
}
