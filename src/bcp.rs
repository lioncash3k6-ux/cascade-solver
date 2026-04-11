//! Stage 2: BCP cascade — pure unit propagation on the augmented CNF.
//!
//! After Stage 1 augmentations (symmetry breaking + cardinality CNF), some
//! formulas are already UNSAT under unit propagation alone. R(4,4)/K_18 is
//! the canonical example: after the cardinality CNF encodes "8 + 8 < 17 at
//! every vertex," BCP derives a contradiction in microseconds without
//! needing CDCL search at all.
//!
//! When the BCP cascade succeeds (verdict = Sat or Unsat), we skip Stage 4
//! (the CDCL backend) entirely. The proof is trivially verifiable —
//! drat-trim's backward checker just runs BCP on the input formula.

use crate::dimacs::Cnf;
use crate::types::{Lit, Var};

#[derive(Debug)]
pub enum BcpResult {
    /// Pure BCP discovered an empty clause / direct contradiction.
    /// `trail` contains the propagated literals in order; the conflict
    /// happened on `conflicting_clause` (index into `cnf.clauses`).
    Unsat {
        trail: Vec<Lit>,
        conflicting_clause: usize,
    },
    /// All variables assigned, no conflict — the assignment is a model.
    Sat { model: Vec<Lit> },
    /// BCP reached a fixpoint without deciding the formula. Some variables
    /// are still unassigned and no clause is unit. Search is required.
    Unresolved {
        trail: Vec<Lit>,
        n_assigned: u32,
        n_unassigned: u32,
    },
}

/// Run unit propagation on a parsed CNF.
///
/// Linear-scan implementation: O(clauses × iterations). For doubly-augmented
/// Ramsey CNFs (~45K clauses for K_18) this is fast enough — milliseconds at
/// worst. A 2WL implementation would be faster but the architectural goal of
/// week 5 is correctness, not maximum throughput.
pub fn bcp_cascade(cnf: &Cnf) -> BcpResult {
    let n = cnf.nvars as usize;
    // assignment[v] = 0 (unassigned) | 1 (true) | -1 (false). Index 0 unused.
    let mut assign = vec![0i8; n + 1];
    let mut trail: Vec<Lit> = Vec::new();

    loop {
        let mut changed = false;
        for (ci, clause) in cnf.clauses.iter().enumerate() {
            // Scan the clause: count unassigned literals, watch for satisfaction.
            let mut unassigned: Option<Lit> = None;
            let mut second_unassigned = false;
            let mut satisfied = false;

            for &lit in clause.lits() {
                let v = lit.var().0 as usize;
                if v == 0 || v > n {
                    // Out-of-range literal — treat as unassigned to be safe.
                    if unassigned.is_none() {
                        unassigned = Some(lit);
                    } else {
                        second_unassigned = true;
                    }
                    continue;
                }
                let cur = assign[v];
                let lit_val = if lit.is_positive() { 1i8 } else { -1i8 };
                if cur == lit_val {
                    satisfied = true;
                    break;
                } else if cur == 0 {
                    if unassigned.is_none() {
                        unassigned = Some(lit);
                    } else {
                        second_unassigned = true;
                        // Can stop scanning early if we've seen 2 unassigned
                        // AND no satisfaction yet.
                    }
                }
                // else: cur == -lit_val → falsified literal, skip
            }

            if satisfied {
                continue;
            }
            if unassigned.is_none() {
                // All literals falsified → conflict
                return BcpResult::Unsat {
                    trail,
                    conflicting_clause: ci,
                };
            }
            if !second_unassigned {
                // Exactly one unassigned literal → propagate
                let lit = unassigned.unwrap();
                let v = lit.var().0 as usize;
                if v > 0 && v <= n {
                    let lit_val = if lit.is_positive() { 1i8 } else { -1i8 };
                    if assign[v] == 0 {
                        assign[v] = lit_val;
                        trail.push(lit);
                        changed = true;
                    } else if assign[v] != lit_val {
                        // Already assigned the opposite — conflict
                        return BcpResult::Unsat {
                            trail,
                            conflicting_clause: ci,
                        };
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Fixpoint reached. Are all variables assigned?
    let mut n_assigned = 0u32;
    let mut n_unassigned = 0u32;
    for v in 1..=n {
        if assign[v] != 0 {
            n_assigned += 1;
        } else {
            n_unassigned += 1;
        }
    }

    if n_unassigned == 0 {
        // Build the model from assignments
        let mut model = Vec::with_capacity(n);
        for v in 1..=n {
            let lit = if assign[v] > 0 {
                Var(v as u32).pos()
            } else {
                Var(v as u32).neg()
            };
            model.push(lit);
        }
        BcpResult::Sat { model }
    } else {
        BcpResult::Unresolved {
            trail,
            n_assigned,
            n_unassigned,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs::parse_reader;
    use std::io::{BufReader, Cursor};

    fn parse(s: &str) -> Cnf {
        parse_reader(BufReader::new(Cursor::new(s.as_bytes()))).unwrap()
    }

    #[test]
    fn bcp_trivial_unsat() {
        // x1 ∧ ¬x1 → conflict via 2 unit clauses
        let cnf = parse("p cnf 1 2\n1 0\n-1 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Unsat { .. } => {}
            other => panic!("expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn bcp_unit_propagation_chain() {
        // x1 ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x3) ∧ ¬x3
        // Should propagate x1 → x2 → x3 → conflict
        let cnf = parse("p cnf 3 4\n1 0\n-1 2 0\n-2 3 0\n-3 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Unsat { trail, .. } => {
                // Trail should have at least x1 (and possibly more before conflict)
                assert!(!trail.is_empty());
            }
            other => panic!("expected Unsat, got {:?}", other),
        }
    }

    #[test]
    fn bcp_full_assignment_sat() {
        // x1 ∧ (x1 ∨ x2) — x1 forces SAT, x2 left unassigned
        let cnf = parse("p cnf 2 2\n1 0\n1 2 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Unresolved { n_assigned, n_unassigned, .. } => {
                assert_eq!(n_assigned, 1);
                assert_eq!(n_unassigned, 1);
            }
            other => panic!("expected Unresolved, got {:?}", other),
        }
    }

    #[test]
    fn bcp_no_progress() {
        // (x1 ∨ x2) ∧ (¬x1 ∨ x2) — no unit propagation possible from level 0
        let cnf = parse("p cnf 2 2\n1 2 0\n-1 2 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Unresolved { trail, .. } => {
                assert!(trail.is_empty());
            }
            other => panic!("expected Unresolved, got {:?}", other),
        }
    }

    #[test]
    fn bcp_single_unit_propagates_to_sat() {
        // x1 ∧ x2: both units, propagate to full assignment.
        let cnf = parse("p cnf 2 2\n1 0\n2 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Sat { model } => {
                assert_eq!(model.len(), 2);
            }
            other => panic!("expected Sat, got {:?}", other),
        }
    }
}
