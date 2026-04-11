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
//!
//! Week 6: two-watched-literals engine. Same public API as the Week 5
//! linear-scan version (BcpResult / bcp_cascade), but propagation is now
//! O(propagated literals · average visited clauses per flip) instead of
//! O(clauses · iterations). On the published R(4,5)/K_25 augmented CNF
//! (600 vars, 66 679 clauses, 134 propagations) the linear-scan version
//! did 134 passes over the whole clause vector; 2WL does a single pass
//! initializing watches and then only visits clauses when one of their
//! two watched literals is falsified.

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

/// Literal index: `2*var` for positive, `2*var + 1` for negative. Var 0 is
/// reserved (invalid input) so indices 0 and 1 are unused.
#[inline]
fn lit_idx(l: Lit) -> usize {
    let v = l.var().0 as usize;
    2 * v + if l.is_negative() { 1 } else { 0 }
}

/// Run unit propagation on a parsed CNF using two-watched-literals.
///
/// The watch invariant: a clause with two or more literals always has its
/// first two slots as the watched literals. When a literal `L` is asserted
/// true on the trail, every clause watching `¬L` is visited; we try to
/// shuffle a non-falsified literal into the watched position. If none is
/// available, the clause is either unit (propagate the other watch) or
/// conflict.
pub fn bcp_cascade(cnf: &Cnf) -> BcpResult {
    let n = cnf.nvars as usize;
    let n_lits = 2 * (n + 1);

    // assign[v] = 0 unassigned, 1 true, -1 false. Index 0 unused.
    let mut assign = vec![0i8; n + 1];
    let mut trail: Vec<Lit> = Vec::new();

    // Mutable copy of the clause database so we can swap watched positions.
    let mut clause_db: Vec<Vec<Lit>> =
        cnf.clauses.iter().map(|c| c.lits().to_vec()).collect();

    // watches[idx] = clause indices to visit when the literal at `idx` is
    // asserted true. If clause C watches w as one of its two slots, C lives
    // in watches[lit_idx(¬w)] because falsifying w is equivalent to
    // asserting ¬w.
    let mut watches: Vec<Vec<usize>> = vec![Vec::new(); n_lits];

    // Initial pass: register watches for ≥2-length clauses, propagate units,
    // and trip immediately on any empty clause.
    for (ci, clause) in clause_db.iter().enumerate() {
        match clause.len() {
            0 => {
                return BcpResult::Unsat {
                    trail,
                    conflicting_clause: ci,
                };
            }
            1 => {
                let lit = clause[0];
                let v = lit.var().0 as usize;
                if v == 0 || v > n {
                    continue;
                }
                let val = if lit.is_positive() { 1i8 } else { -1i8 };
                if assign[v] == 0 {
                    assign[v] = val;
                    trail.push(lit);
                } else if assign[v] != val {
                    return BcpResult::Unsat {
                        trail,
                        conflicting_clause: ci,
                    };
                }
            }
            _ => {
                let w1 = clause[0];
                let w2 = clause[1];
                watches[lit_idx(w1.negate())].push(ci);
                watches[lit_idx(w2.negate())].push(ci);
            }
        }
    }

    // Main propagation loop. Re-use the trail vector as an implicit queue by
    // advancing `prop_head`.
    let mut prop_head: usize = 0;
    while prop_head < trail.len() {
        let lit = trail[prop_head];
        prop_head += 1;
        let lit_i = lit_idx(lit);
        let neg = lit.negate();

        // Take the current watch list out so we can freely mutate
        // `watches[..]` while iterating (clauses that stay on this list get
        // pushed back; clauses that move get pushed to a different index).
        let old_watches = std::mem::take(&mut watches[lit_i]);

        'clause_loop: for &ci in old_watches.iter() {
            let clause = &mut clause_db[ci];

            // Put the falsified watched literal in slot 1 so slot 0 is always
            // "the other watch."
            if clause[0] == neg {
                clause.swap(0, 1);
            }

            let other = clause[0];
            let other_v = other.var().0 as usize;
            let other_val = if other.is_positive() { 1i8 } else { -1i8 };

            // Fast path: the other watched literal is already satisfied.
            // Nothing to do — keep the clause on this watch list.
            if other_v > 0 && other_v <= n && assign[other_v] == other_val {
                watches[lit_i].push(ci);
                continue;
            }

            // Scan the rest of the clause for a non-falsified literal to
            // promote to the watched position.
            for j in 2..clause.len() {
                let l = clause[j];
                let v = l.var().0 as usize;
                if v == 0 || v > n {
                    // Out-of-range literal — be defensive and treat as a
                    // valid (effectively unassigned) watch.
                    clause.swap(1, j);
                    let new_watch_idx = lit_idx(clause[1].negate());
                    watches[new_watch_idx].push(ci);
                    continue 'clause_loop;
                }
                let l_val = if l.is_positive() { 1i8 } else { -1i8 };
                if assign[v] != -l_val {
                    // Not falsified — promote to the watch slot.
                    clause.swap(1, j);
                    let new_watch_idx = lit_idx(clause[1].negate());
                    watches[new_watch_idx].push(ci);
                    continue 'clause_loop;
                }
            }

            // Fell through: every other literal is falsified. The clause is
            // either unit on `other` or conflicting. Either way it stays on
            // this watch list.
            watches[lit_i].push(ci);

            if other_v == 0 || other_v > n {
                continue;
            }
            match assign[other_v] {
                0 => {
                    assign[other_v] = other_val;
                    trail.push(other);
                }
                cur if cur == other_val => {}
                _ => {
                    return BcpResult::Unsat {
                        trail,
                        conflicting_clause: ci,
                    };
                }
            }
        }
    }

    // Fixpoint reached. Partition variables into assigned vs unassigned.
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
            BcpResult::Unresolved {
                n_assigned,
                n_unassigned,
                ..
            } => {
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

    #[test]
    fn bcp_binary_clause_propagation() {
        // Binary clauses only — exercises the "no clause[2..] to scan" path.
        // x1 ∧ (¬x1 ∨ x2) ∧ (¬x2 ∨ x3) — should propagate to x1,x2,x3 all true
        let cnf = parse("p cnf 3 3\n1 0\n-1 2 0\n-2 3 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Sat { model } => {
                assert_eq!(model.len(), 3);
                assert!(model.iter().all(|l| l.is_positive()));
            }
            other => panic!("expected Sat, got {:?}", other),
        }
    }

    #[test]
    fn bcp_long_clause_rewatch() {
        // Long clause (¬x1 ∨ ¬x2 ∨ x3 ∨ x4 ∨ x5) with x1 and x2 forced true.
        // After x1 is propagated, the watch on ¬x1 must shuffle to x3/x4/x5.
        // After x2 is propagated, the other watch must also shuffle.
        // Result: x3, x4, x5 all remain unassigned (clause stays non-unit).
        let cnf = parse("p cnf 5 3\n1 0\n2 0\n-1 -2 3 4 5 0\n");
        match bcp_cascade(&cnf) {
            BcpResult::Unresolved {
                n_assigned,
                n_unassigned,
                ..
            } => {
                assert_eq!(n_assigned, 2);
                assert_eq!(n_unassigned, 3);
            }
            other => panic!("expected Unresolved, got {:?}", other),
        }
    }
}
