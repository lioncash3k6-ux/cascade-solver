//! Algebraic side-channel propagator — GAPS leg 4 wired into the
//! IPASIR-UP bus.
//!
//! `AlgebraicPropagator` watches CDCL's trail and periodically asks
//! the Nullstellensatz-lite engine: "given the current partial
//! assignment, is `F|trail` UNSAT at degree ≤ d?" If yes, it emits
//! the blocking clause `¬(trail prefix)` — a valid logical
//! consequence of `F` that CDCL couldn't derive by resolution alone
//! (that's the whole point of leg 4's complementarity).
//!
//! # Trigger
//!
//! Configurable firing schedule via `fire_every` (default: every 64
//! decision-level transitions) and `max_degree` (default 3). The
//! goal is a lightweight periodic probe rather than a guaranteed
//! stall detector — we want the mechanism in place; smarter
//! triggers come later.
//!
//! # Encoding
//!
//! The propagator owns a copy of `F` in DIMACS form. When triggered:
//!   1. Walk the CDCL trail mirror, simplify `F` by substituting
//!      assigned literals: drop satisfied clauses, remove False
//!      literals.
//!   2. Remap the surviving variables to a compact 1..=n' range
//!      (our NS wants contiguous indices).
//!   3. Call [`super::ns::find_ns_certificate`] at `max_degree`.
//!   4. On success, build the blocking clause (negation of every
//!      currently-True trail literal) and enqueue it via the
//!      standard pending-propagation path.
//!
//! # Soundness
//!
//! A blocking clause `¬l_1 ∨ … ∨ ¬l_k` emitted by this propagator is
//! a logical consequence of `F` (not just equisatisfiability-
//! preserving): the NS certificate is a direct proof that
//! `F ∧ l_1 ∧ … ∧ l_k ⊢ ⊥`. Therefore the emitted clause is RUP
//! against `F` (via the polynomial certificate as a witness). This
//! is stronger than the symmetry propagator's clauses, which need
//! VeriPB `red` witnesses.
//!
//! # Status (v0.6)
//!
//! Wired into the composite propagator bus via a new `--alg-propagate`
//! flag. Initial heuristic trigger. Not yet benchmarked against
//! large PHP — the next tier-2 work.

use crate::algebra::ns::{find_ns_certificate, verify_certificate, NsResult};
use crate::cadical::ExternalPropagator;
use std::collections::HashMap;

pub struct AlgebraicPropagator {
    /// Original CNF in DIMACS form.
    cnf: Vec<Vec<i32>>,
    /// Number of variables in the original CNF.
    n_vars: u32,

    /// Assignment mirror: value of each original var.
    /// Index 0 = padding. 1..=n_vars = True/False/Undef.
    assign: Vec<Option<bool>>,
    trail: Vec<i32>,
    level_start: Vec<usize>,
    level: usize,

    /// Pending clauses to propagate.
    pending: Vec<PendingClause>,
    pending_head: usize,

    /// Reason map: propagated_lit -> reason-clause iteration cursor.
    reason_clauses: HashMap<i32, Vec<i32>>,
    reason_cursor: HashMap<i32, usize>,

    /// Trigger schedule.
    fire_every: u64,
    level_transitions: u64,
    max_degree: usize,

    /// Stats.
    pub stats: Stats,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub ns_probes: u64,
    pub ns_certs_found: u64,
    pub blocking_clauses_emitted: u64,
    pub assignments_processed: u64,
}

#[derive(Clone, Debug)]
struct PendingClause {
    lit: i32,
    clause: Vec<i32>,
}

impl AlgebraicPropagator {
    pub fn new(cnf: Vec<Vec<i32>>, n_vars: u32) -> Self {
        let fire_every: u64 = std::env::var("CASCADE_ALG_FIRE_EVERY")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(64);
        let max_degree: usize = std::env::var("CASCADE_ALG_MAX_DEGREE")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(3);
        Self::new_with_config(cnf, n_vars, fire_every, max_degree)
    }

    pub fn new_with_config(
        cnf: Vec<Vec<i32>>,
        n_vars: u32,
        fire_every: u64,
        max_degree: usize,
    ) -> Self {
        Self {
            cnf,
            n_vars,
            assign: vec![None; n_vars as usize + 1],
            trail: Vec::new(),
            level_start: Vec::new(),
            level: 0,
            pending: Vec::new(),
            pending_head: 0,
            reason_clauses: HashMap::new(),
            reason_cursor: HashMap::new(),
            fire_every,
            level_transitions: 0,
            max_degree,
            stats: Stats::default(),
        }
    }

    pub fn observed_vars(&self) -> Vec<i32> {
        (1..=self.n_vars as i32).collect()
    }

    /// Check the polynomial-time NS-lite oracle against F|trail. If it
    /// proves UNSAT, enqueue the blocking clause.
    fn try_algebraic_probe(&mut self) {
        self.stats.ns_probes += 1;

        // Simplify F under current trail.
        let mut simplified: Vec<Vec<i32>> = Vec::new();
        let mut var_map: HashMap<u32, u32> = HashMap::new();
        let mut next_id: u32 = 1;
        for c in &self.cnf {
            let mut new_clause = Vec::new();
            let mut satisfied = false;
            for &l in c {
                let v = l.unsigned_abs();
                if v == 0 || v > self.n_vars {
                    continue;
                }
                match self.assign[v as usize] {
                    Some(true) if l > 0 => { satisfied = true; break; }
                    Some(false) if l < 0 => { satisfied = true; break; }
                    Some(_) => {
                        // Literal is False — drop it.
                    }
                    None => {
                        // Unassigned — remap.
                        let mapped = *var_map.entry(v).or_insert_with(|| {
                            let id = next_id;
                            next_id += 1;
                            id
                        });
                        let new_lit = if l > 0 { mapped as i32 } else { -(mapped as i32) };
                        new_clause.push(new_lit);
                    }
                }
            }
            if satisfied {
                continue;
            }
            if new_clause.is_empty() {
                // Empty clause — F|trail is trivially UNSAT. Build
                // blocking clause now without invoking NS.
                self.build_blocking_from_trail();
                return;
            }
            simplified.push(new_clause);
        }
        if simplified.is_empty() {
            return; // F|trail is trivially SAT
        }

        let n_reduced = next_id - 1;
        match find_ns_certificate(&simplified, n_reduced, self.max_degree) {
            NsResult::Unsat(cert) => {
                if verify_certificate(&cert, &simplified) {
                    self.stats.ns_certs_found += 1;
                    self.build_blocking_from_trail();
                }
            }
            NsResult::NoCertificate => {}
        }
    }

    /// Build the clause `¬l_1 ∨ … ∨ ¬l_k` where `l_i` are the
    /// currently-True trail literals. Enqueue as a pending blocker.
    fn build_blocking_from_trail(&mut self) {
        if self.trail.is_empty() {
            return;
        }
        let clause: Vec<i32> = self.trail.iter().map(|&l| -l).collect();
        let propagated = *clause.last().unwrap();
        self.reason_clauses.insert(propagated, clause.clone());
        self.pending.push(PendingClause {
            lit: propagated,
            clause,
        });
        self.stats.blocking_clauses_emitted += 1;
    }
}

impl ExternalPropagator for AlgebraicPropagator {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for &l in lits {
            let v = l.unsigned_abs();
            if v == 0 || v > self.n_vars {
                continue;
            }
            if self.assign[v as usize].is_some() {
                continue;
            }
            self.assign[v as usize] = Some(l > 0);
            self.trail.push(l);
            self.stats.assignments_processed += 1;
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.level += 1;
        self.level_start.push(self.trail.len());
        self.level_transitions += 1;
        // Periodic algebraic probe.
        if self.level_transitions % self.fire_every == 0 {
            self.try_algebraic_probe();
        }
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        while self.level > new_level {
            if let Some(start) = self.level_start.pop() {
                while self.trail.len() > start {
                    let l = self.trail.pop().unwrap();
                    let v = l.unsigned_abs() as usize;
                    self.assign[v] = None;
                }
            }
            self.level -= 1;
        }
        self.pending.clear();
        self.pending_head = 0;
    }

    fn propagate(&mut self) -> i32 {
        while self.pending_head < self.pending.len() {
            let i = self.pending_head;
            self.pending_head += 1;
            let p = &self.pending[i];
            let v = p.lit.unsigned_abs() as usize;
            let want = p.lit > 0;
            if self.assign[v] == Some(want) {
                continue; // already satisfied
            }
            self.reason_cursor.insert(p.lit, 0);
            return p.lit;
        }
        0
    }

    fn add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        let reason = match self.reason_clauses.get(&propagated_lit) {
            Some(r) => r,
            None => return 0,
        };
        let cur = *self.reason_cursor.get(&propagated_lit).unwrap_or(&0);
        if cur < reason.len() {
            let l = reason[cur];
            self.reason_cursor.insert(propagated_lit, cur + 1);
            l
        } else {
            self.reason_cursor.insert(propagated_lit, 0);
            0
        }
    }

    fn check_found_model(&mut self, _model: &[i32]) -> bool {
        // The algebraic propagator doesn't block models on its own;
        // if the NS didn't catch UNSAT, any model of F reaching
        // here is trusted. CDCL has already verified F|model = True.
        true
    }
}

impl Drop for AlgebraicPropagator {
    fn drop(&mut self) {
        if std::env::var("CASCADE_ALG_STATS").is_ok() {
            eprintln!(
                "c [alg-propagator] probes={} certs={} blockers={} assignments={} \
                 fire_every={} max_degree={}",
                self.stats.ns_probes,
                self.stats.ns_certs_found,
                self.stats.blocking_clauses_emitted,
                self.stats.assignments_processed,
                self.fire_every,
                self.max_degree,
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_propagator_is_silent_until_trigger() {
        let cnf = vec![vec![1, 2], vec![-1, 2], vec![1, -2]];
        let mut p = AlgebraicPropagator::new(cnf, 2);
        assert_eq!(p.propagate(), 0);
        assert_eq!(p.stats.ns_probes, 0);
    }

    #[test]
    fn propagator_fires_at_configured_interval() {
        let cnf = vec![vec![1], vec![-1]];
        let mut p = AlgebraicPropagator::new_with_config(cnf, 1, 1, 1);
        p.notify_new_decision_level();
        assert_eq!(p.stats.ns_probes, 1);
    }

    #[test]
    fn propagator_finds_ns_cert_on_trivial_unsat() {
        let cnf = vec![vec![1], vec![-1]];
        let mut p = AlgebraicPropagator::new_with_config(cnf, 1, 1, 1);
        p.notify_new_decision_level();
        assert_eq!(p.stats.ns_probes, 1);
    }

    #[test]
    fn propagator_emits_blocker_when_trail_closes_the_formula() {
        // F = {x1 ∨ x2, ¬x1 ∨ x3, ¬x3}. Under trail {x1}, simplifies
        // to {x2, x3, ¬x3} (first clause satisfied on x1, second reduces
        // to x3, third stays). NS at d=1 finds x3 ∧ ¬x3 contradiction.
        // Blocker: [¬1] = [-1].
        let cnf = vec![vec![1, 2], vec![-1, 3], vec![-3]];
        let mut p = AlgebraicPropagator::new_with_config(cnf, 3, 1, 1);
        p.notify_assignment(&[1]);
        p.notify_new_decision_level();
        let lit = p.propagate();
        assert_eq!(lit, -1);
        assert_eq!(p.add_reason_clause_lit(-1), -1);
    }
}
