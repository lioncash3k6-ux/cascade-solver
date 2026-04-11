//! Layer 2: Augmentation IR — a clause with a proof justification.
//!
//! Every clause in the formula (input or derived) carries a justification
//! describing WHY it's there. The proof writer uses these to emit LRAT/DRAT/DSR.

use crate::types::{Clause, ClauseId, Lit, Var};

/// One clause + its justification.
#[derive(Clone, Debug)]
pub struct Augmentation {
    pub id: ClauseId,
    pub clause: Clause,
    pub justification: Justification,
}

/// How was this clause obtained? Determines what proof step to emit.
#[derive(Clone, Debug)]
pub enum Justification {
    /// An axiom from the input CNF. No proof step needed; it's in the
    /// problem file that the verifier reads as input.
    Input,

    /// Reverse Unit Propagation: there exist clause IDs whose unit-propagation
    /// chain (starting from the negation of this clause) derives a conflict.
    /// `hints` are the clause IDs in propagation order (LRAT format).
    Rup { hints: Vec<ClauseId> },

    /// Resolution Asymmetric Tautology: like RUP but with a pivot literal
    /// indicating which variable's negation triggers the propagation chain.
    Rat { pivot: Lit, hints: Vec<ClauseId> },

    /// Substitution Redundancy (SR/DSR): a witness substitution σ such that
    /// the clause is redundant under σ. Used for symmetry-breaking additions.
    Sr {
        witness: Substitution,
        hints: Vec<ClauseId>,
    },

    /// Propagation Redundancy: extension variable definition, with a witness
    /// that's the assignment defining the new variable.
    Pr {
        witness: Substitution,
        hints: Vec<ClauseId>,
    },

    /// A clause derived by a propagator (cardinality, biclique, lex, etc).
    /// The propagator name is recorded for diagnostic purposes; the actual
    /// proof step is one of the above.
    Propagator {
        name: &'static str,
        inner: Box<Justification>,
    },

    /// A deletion event. The clause is being removed from the active set.
    Delete,
}

/// A variable -> literal substitution, used for SR/PR witnesses.
#[derive(Clone, Debug)]
pub struct Substitution {
    /// `pairs[i] = (var, target)` means the witness substitutes `var := target`.
    /// Vars not in the list are mapped to themselves.
    pub pairs: Vec<(Var, Lit)>,
}

impl Substitution {
    pub fn empty() -> Self {
        Substitution { pairs: Vec::new() }
    }

    pub fn from_vertex_transposition(a: u32, b: u32, n: u32) -> Self {
        // For Ramsey-style problems: vertex transposition (a,b) induces
        // an edge permutation. This is a placeholder — full implementation
        // belongs in a Ramsey-specific helper.
        let _ = (a, b, n);
        Substitution::empty()
    }
}

impl Justification {
    /// Is this an axiom? (No proof step required.)
    pub fn is_axiom(&self) -> bool {
        matches!(self, Justification::Input)
    }
}

/// The Augmentation IR is a sequence of these, in proof order.
#[derive(Default, Debug)]
pub struct AugmentationIr {
    steps: Vec<Augmentation>,
    next_id: u64,
}

impl AugmentationIr {
    pub fn new() -> Self {
        AugmentationIr {
            steps: Vec::new(),
            next_id: 1,
        }
    }

    /// Allocate a fresh clause ID and push the augmentation.
    pub fn add(&mut self, clause: Clause, justification: Justification) -> ClauseId {
        let id = ClauseId::new(self.next_id);
        self.next_id += 1;
        self.steps.push(Augmentation {
            id,
            clause,
            justification,
        });
        id
    }

    pub fn steps(&self) -> &[Augmentation] {
        &self.steps
    }

    pub fn len(&self) -> usize {
        self.steps.len()
    }

    pub fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn add_input_clauses() {
        let mut ir = AugmentationIr::new();
        let c1 = ir.add(
            Clause::new(vec![Lit::new(1), Lit::new(-2)]),
            Justification::Input,
        );
        let c2 = ir.add(
            Clause::new(vec![Lit::new(2), Lit::new(3)]),
            Justification::Input,
        );
        assert_eq!(c1, ClauseId::new(1));
        assert_eq!(c2, ClauseId::new(2));
        assert_eq!(ir.len(), 2);
    }
}
