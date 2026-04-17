//! CompositePropagator — a fan-out/router for multiple IPASIR-UP sub-propagators.
//!
//! CaDiCaL's external-propagator API accepts a single `ExternalPropagator`.
//! v0.6 needs two sub-propagators running simultaneously (biclique ban-clauses
//! and online symmetry enforcement), and v0.7+ will add more (algebraic,
//! hierarchical). `CompositePropagator` wraps a `Vec<Box<dyn ExternalPropagator>>`
//! and presents the same trait to CaDiCaL while routing calls to each sub.
//!
//! # Semantics
//!
//! * **Broadcast callbacks** — `notify_assignment`, `notify_new_decision_level`,
//!   `notify_backtrack` fan out to every sub in registration order.
//! * **Round-robin propagate** — `propagate()` visits subs starting from an
//!   internal cursor and returns the first non-zero literal. Cursor advances
//!   after each returned lit. Prevents starvation under adversarial ordering:
//!   a sub that only has one propagation still gets drained before a
//!   high-volume sub monopolizes the pipe.
//! * **Reason routing** — when a sub returns a lit from `propagate()`, we
//!   record `lit -> sub_idx`. `add_reason_clause_lit(lit)` is routed to that
//!   sub. The sub maintains its own position within the reason clause; we
//!   only route. If the same lit is later re-propagated (post-backjump), the
//!   map entry is overwritten.
//! * **Model check** — `check_found_model` is the logical AND across subs:
//!   a model is accepted iff every sub accepts it. Short-circuits on the
//!   first rejection.
//!
//! # Non-goals
//!
//! * Cross-sub clause synthesis (that's RFC-0002 territory — orbit-closed
//!   learning across symmetry, etc.). The composite is strictly a router.
//! * Parallelism. Subs are called sequentially from CaDiCaL's single thread.

use crate::cadical::ExternalPropagator;
use std::collections::HashMap;

pub struct CompositePropagator {
    subs: Vec<Box<dyn ExternalPropagator>>,
    cursor: usize,
    /// propagated literal -> index of the sub that produced it
    reason_owner: HashMap<i32, usize>,
}

impl CompositePropagator {
    pub fn new() -> Self {
        Self {
            subs: Vec::new(),
            cursor: 0,
            reason_owner: HashMap::new(),
        }
    }

    pub fn with_subs(subs: Vec<Box<dyn ExternalPropagator>>) -> Self {
        Self {
            subs,
            cursor: 0,
            reason_owner: HashMap::new(),
        }
    }

    pub fn push(&mut self, sub: Box<dyn ExternalPropagator>) {
        self.subs.push(sub);
    }

    pub fn len(&self) -> usize {
        self.subs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.subs.is_empty()
    }
}

impl Default for CompositePropagator {
    fn default() -> Self {
        Self::new()
    }
}

impl ExternalPropagator for CompositePropagator {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for sub in &mut self.subs {
            sub.notify_assignment(lits);
        }
    }

    fn notify_new_decision_level(&mut self) {
        for sub in &mut self.subs {
            sub.notify_new_decision_level();
        }
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        for sub in &mut self.subs {
            sub.notify_backtrack(new_level);
        }
    }

    fn propagate(&mut self) -> i32 {
        let n = self.subs.len();
        if n == 0 {
            return 0;
        }
        for offset in 0..n {
            let idx = (self.cursor + offset) % n;
            let lit = self.subs[idx].propagate();
            if lit != 0 {
                self.reason_owner.insert(lit, idx);
                self.cursor = (idx + 1) % n;
                return lit;
            }
        }
        0
    }

    fn add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        if let Some(&idx) = self.reason_owner.get(&propagated_lit) {
            self.subs[idx].add_reason_clause_lit(propagated_lit)
        } else {
            // No recorded owner: this is a contract violation on CaDiCaL's
            // part (asking for a reason for a lit we never returned) OR
            // the entry was cleared. Returning 0 terminates the clause
            // cleanly; the solver will treat it as a unit reason { lit }.
            0
        }
    }

    fn check_found_model(&mut self, model: &[i32]) -> bool {
        for sub in &mut self.subs {
            if !sub.check_found_model(model) {
                return false;
            }
        }
        true
    }

    fn learning(&mut self, size: i32) -> bool {
        self.subs.iter_mut().any(|s| s.learning(size))
    }

    fn learn_clause_lit(&mut self, lit: i32) {
        for sub in &mut self.subs {
            sub.learn_clause_lit(lit);
        }
    }

    fn has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        for sub in &mut self.subs {
            if sub.has_external_clause(is_forgettable) {
                return true;
            }
        }
        false
    }

    fn add_external_clause_lit(&mut self) -> i32 {
        for sub in &mut self.subs {
            let lit = sub.add_external_clause_lit();
            if lit != 0 {
                return lit;
            }
        }
        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Mock sub-propagator that emits a scripted sequence of propagations and
    // records callbacks for assertion.
    struct MockSub {
        name: &'static str,
        scripted: Vec<i32>, // pops from the front on each propagate() call
        assignments_seen: Vec<i32>,
        decision_levels: u32,
        backtracks: Vec<usize>,
        reason_map: std::collections::HashMap<i32, Vec<i32>>,
        reason_cursor: std::collections::HashMap<i32, usize>,
        model_verdict: bool,
    }

    impl MockSub {
        fn new(name: &'static str, scripted: Vec<i32>) -> Self {
            Self {
                name,
                scripted,
                assignments_seen: Vec::new(),
                decision_levels: 0,
                backtracks: Vec::new(),
                reason_map: std::collections::HashMap::new(),
                reason_cursor: std::collections::HashMap::new(),
                model_verdict: true,
            }
        }

        fn with_reason(mut self, lit: i32, clause: Vec<i32>) -> Self {
            self.reason_map.insert(lit, clause);
            self
        }

        fn reject_models(mut self) -> Self {
            self.model_verdict = false;
            self
        }
    }

    impl ExternalPropagator for MockSub {
        fn notify_assignment(&mut self, lits: &[i32]) {
            self.assignments_seen.extend_from_slice(lits);
        }
        fn notify_new_decision_level(&mut self) {
            self.decision_levels += 1;
        }
        fn notify_backtrack(&mut self, new_level: usize) {
            self.backtracks.push(new_level);
        }
        fn propagate(&mut self) -> i32 {
            if self.scripted.is_empty() { 0 } else { self.scripted.remove(0) }
        }
        fn add_reason_clause_lit(&mut self, lit: i32) -> i32 {
            let cur = *self.reason_cursor.entry(lit).or_insert(0);
            let out = match self.reason_map.get(&lit) {
                Some(cl) if cur < cl.len() => cl[cur],
                _ => 0,
            };
            if out == 0 {
                self.reason_cursor.insert(lit, 0);
            } else {
                self.reason_cursor.insert(lit, cur + 1);
            }
            out
        }
        fn check_found_model(&mut self, _m: &[i32]) -> bool {
            self.model_verdict
        }
    }

    #[test]
    fn empty_composite_propagates_zero() {
        let mut c = CompositePropagator::new();
        assert_eq!(c.propagate(), 0);
    }

    #[test]
    fn single_sub_is_transparent() {
        let sub = MockSub::new("s", vec![5, 7, -3]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(sub)]);
        assert_eq!(c.propagate(), 5);
        assert_eq!(c.propagate(), 7);
        assert_eq!(c.propagate(), -3);
        assert_eq!(c.propagate(), 0);
    }

    #[test]
    fn round_robin_interleaves_two_subs() {
        // Sub A has three props; Sub B has two. Round-robin should give
        // A, B, A, B, A — not A, A, A, B, B.
        let a = MockSub::new("A", vec![1, 2, 3]);
        let b = MockSub::new("B", vec![10, 20]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);
        let mut out = Vec::new();
        loop {
            let l = c.propagate();
            if l == 0 { break; }
            out.push(l);
        }
        assert_eq!(out, vec![1, 10, 2, 20, 3]);
    }

    #[test]
    fn round_robin_skips_empty_sub() {
        // Sub A empty, Sub B has props. Should drain B entirely.
        let a = MockSub::new("A", vec![]);
        let b = MockSub::new("B", vec![42, 43]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);
        assert_eq!(c.propagate(), 42);
        assert_eq!(c.propagate(), 43);
        assert_eq!(c.propagate(), 0);
    }

    #[test]
    fn broadcast_notify_assignment_reaches_every_sub() {
        let a = MockSub::new("A", vec![]);
        let b = MockSub::new("B", vec![]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);
        c.notify_assignment(&[1, -2, 3]);
        // We can't downcast through Box<dyn>, but we can reach through via
        // another propagate round to confirm no state was poisoned.
        assert_eq!(c.propagate(), 0);
        // Direct test: reconstruct with owned mocks we can inspect via a
        // Vec<Rc<RefCell<MockSub>>>-style pattern. For simplicity, just
        // assert the shape. Detailed assertion is exercised in
        // broadcast_decision_levels and broadcast_backtracks below using
        // a second path.
    }

    // Helper: a shared-state mock via Arc<Mutex<...>>, so we can inspect
    // post-hoc from the test without downcasting.
    struct SharedMock {
        inner: std::sync::Arc<std::sync::Mutex<MockSub>>,
    }
    impl ExternalPropagator for SharedMock {
        fn notify_assignment(&mut self, lits: &[i32]) {
            self.inner.lock().unwrap().notify_assignment(lits);
        }
        fn notify_new_decision_level(&mut self) {
            self.inner.lock().unwrap().notify_new_decision_level();
        }
        fn notify_backtrack(&mut self, n: usize) {
            self.inner.lock().unwrap().notify_backtrack(n);
        }
        fn propagate(&mut self) -> i32 {
            self.inner.lock().unwrap().propagate()
        }
        fn add_reason_clause_lit(&mut self, l: i32) -> i32 {
            self.inner.lock().unwrap().add_reason_clause_lit(l)
        }
        fn check_found_model(&mut self, m: &[i32]) -> bool {
            self.inner.lock().unwrap().check_found_model(m)
        }
    }

    #[test]
    fn broadcast_assignments_and_levels_and_backtracks() {
        use std::sync::{Arc, Mutex};
        let a = Arc::new(Mutex::new(MockSub::new("A", vec![])));
        let b = Arc::new(Mutex::new(MockSub::new("B", vec![])));
        let mut c = CompositePropagator::with_subs(vec![
            Box::new(SharedMock { inner: a.clone() }),
            Box::new(SharedMock { inner: b.clone() }),
        ]);
        c.notify_assignment(&[1, -2]);
        c.notify_new_decision_level();
        c.notify_new_decision_level();
        c.notify_backtrack(1);

        for lock in [&a, &b] {
            let g = lock.lock().unwrap();
            assert_eq!(g.assignments_seen, vec![1, -2]);
            assert_eq!(g.decision_levels, 2);
            assert_eq!(g.backtracks, vec![1]);
        }
    }

    #[test]
    fn reason_routing_to_correct_sub() {
        // A propagates lit 7 with reason [7, -1, -2].
        // B propagates lit 8 with reason [8, -3].
        // After both are propagated, CaDiCaL asks for reasons in either
        // order; composite must route each lit back to its owner.
        let a = MockSub::new("A", vec![7]).with_reason(7, vec![7, -1, -2]);
        let b = MockSub::new("B", vec![8]).with_reason(8, vec![8, -3]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);

        assert_eq!(c.propagate(), 7);
        assert_eq!(c.propagate(), 8);

        // Reason for 7 (in order)
        assert_eq!(c.add_reason_clause_lit(7), 7);
        assert_eq!(c.add_reason_clause_lit(7), -1);
        assert_eq!(c.add_reason_clause_lit(7), -2);
        assert_eq!(c.add_reason_clause_lit(7), 0); // clause terminator

        // Interleaved with reason for 8
        assert_eq!(c.add_reason_clause_lit(8), 8);
        assert_eq!(c.add_reason_clause_lit(8), -3);
        assert_eq!(c.add_reason_clause_lit(8), 0);
    }

    #[test]
    fn reason_for_unknown_lit_returns_zero() {
        let mut c = CompositePropagator::new();
        assert_eq!(c.add_reason_clause_lit(99), 0);
    }

    #[test]
    fn check_model_requires_unanimous_acceptance() {
        // A accepts, B rejects → composite rejects.
        let a = MockSub::new("A", vec![]);
        let b = MockSub::new("B", vec![]).reject_models();
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);
        assert!(!c.check_found_model(&[1, 2, 3]));

        // Both accept → composite accepts.
        let a = MockSub::new("A", vec![]);
        let b = MockSub::new("B", vec![]);
        let mut c = CompositePropagator::with_subs(vec![Box::new(a), Box::new(b)]);
        assert!(c.check_found_model(&[1, 2, 3]));
    }

    #[test]
    fn cursor_wraparound_after_full_drain() {
        // Three subs: first round drains one item from each; second round
        // starts where first left off and should produce remaining items in
        // the same rotation.
        let a = MockSub::new("A", vec![1, 2]);
        let b = MockSub::new("B", vec![10]);
        let d = MockSub::new("D", vec![100, 200, 300]);
        let mut c = CompositePropagator::with_subs(vec![
            Box::new(a),
            Box::new(b),
            Box::new(d),
        ]);
        let mut out = Vec::new();
        loop {
            let l = c.propagate();
            if l == 0 { break; }
            out.push(l);
        }
        // Expected rotation: A(1), B(10), D(100), A(2), B(0→skip), D(200), D(300)
        //                                                   ^skipped because cursor advances past empty
        assert_eq!(out, vec![1, 10, 100, 2, 200, 300]);
    }
}
