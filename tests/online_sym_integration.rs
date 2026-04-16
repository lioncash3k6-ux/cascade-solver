//! End-to-end test for PR-4: SymmetryPropagator running live inside
//! CaDiCaL via CompositePropagator.
//!
//! Scenario: R(3,3)/K_6 with triangle ban clauses in the CNF and two
//! propagators attached:
//!   1. BicliquePropagator — ban-clause groups (v0.5 behavior)
//!   2. SymmetryPropagator — live lex-leader enforcement (PR-4)
//!
//! Acceptance criteria:
//!   * Verdict remains UNSAT.
//!   * The composite does not crash, hang, or produce a wrong answer.
//!   * The propagator's stats report at least one violation fired
//!     (proves the sym propagator is actually active, not silently
//!     no-op'ing).
//!
//! We don't compare conflict counts against v0.5 in this test — that's
//! the benchmark in a separate harness. Here we only gate correctness.

use cascade::biclique;
use cascade::cadical::{ExternalPropagator, Solver, SolveResult};
use cascade::cardinality::ev;
use cascade::propagator::{BicliquePropagator, CompositePropagator};
use cascade::symmetry::{GeneratorSet, Permutation, SymmetryPropagator};

fn r33_triangle_bans(n: u32) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    for a in 1..=n {
        for b in (a + 1)..=n {
            for c in (b + 1)..=n {
                let eab = ev(a, b, n).raw();
                let eac = ev(a, c, n).raw();
                let ebc = ev(b, c, n).raw();
                out.push(vec![-eab, -eac, -ebc]);
                out.push(vec![eab, eac, ebc]);
            }
        }
    }
    out
}

fn feed_clauses(solver: &mut Solver, clauses: &[Vec<i32>]) {
    for c in clauses {
        for &l in c {
            solver.add(l);
        }
        solver.add(0);
    }
}

/// Hand-crafted color-swap generator for R(3,3)/K_6: x_i -> ~x_i.
fn color_swap_generator_k6() -> GeneratorSet {
    let n_vars = 15u32;
    let pairs: Vec<_> = (1..=n_vars).map(|v| (v, -(v as i32))).collect();
    let mut gs = GeneratorSet::empty(n_vars);
    gs.push(Permutation::from_mapping(n_vars, &pairs));
    gs
}

#[test]
fn r33_k6_with_sym_only_returns_unsat() {
    // Sym propagator alone (no biclique). Sanity: still UNSAT.
    let n = 6;
    let gs = color_swap_generator_k6();
    let mut sym = SymmetryPropagator::new(gs);
    let observed = sym.observed_vars();
    let _ = &mut sym; // silence unused-mut before move

    let mut solver = Solver::new();
    feed_clauses(&mut solver, &r33_triangle_bans(n));
    solver.connect_propagator(Box::new(sym) as Box<dyn ExternalPropagator>, &observed);
    assert_eq!(solver.solve(), SolveResult::Unsat);
}

#[test]
fn r33_k6_composite_biclique_plus_sym_unsat() {
    let n = 6;
    let decomp = biclique::decompose(n, 3, 3);
    let observed_bicl: Vec<i32> = (1..=decomp.n_edges as i32).collect();
    let bicl = BicliquePropagator::new(decomp);

    let gs = color_swap_generator_k6();
    let sym = SymmetryPropagator::new(gs);
    let observed_sym = sym.observed_vars();

    // Observed union (both propagators observe edge vars 1..=15).
    let mut observed = observed_bicl.clone();
    for v in &observed_sym {
        if !observed.contains(v) {
            observed.push(*v);
        }
    }

    let mut comp = CompositePropagator::new();
    comp.push(Box::new(bicl));
    comp.push(Box::new(sym));

    let mut solver = Solver::new();
    feed_clauses(&mut solver, &r33_triangle_bans(n));
    solver.connect_propagator(Box::new(comp) as Box<dyn ExternalPropagator>, &observed);
    assert_eq!(solver.solve(), SolveResult::Unsat);
}

#[test]
fn r33_k6_sym_propagator_actually_fires() {
    // Construct the sym propagator with ordering [1, 2, 3, ...] (default)
    // and color-swap generator. Under color-swap, any model with v1=True
    // must be blocked — so the propagator's violation counter should be
    // non-zero by the time CaDiCaL reaches UNSAT.
    //
    // We can't read back the propagator's stats after connect_propagator
    // (it's been moved into the solver). So we use a shared-state shim:
    // wrap in an Arc<Mutex<SymmetryPropagator>> and expose via a thin
    // adapter that forwards calls.
    use std::sync::{Arc, Mutex};

    struct Shim(Arc<Mutex<SymmetryPropagator>>);
    impl ExternalPropagator for Shim {
        fn notify_assignment(&mut self, lits: &[i32]) {
            self.0.lock().unwrap().notify_assignment(lits);
        }
        fn notify_new_decision_level(&mut self) {
            self.0.lock().unwrap().notify_new_decision_level();
        }
        fn notify_backtrack(&mut self, n: usize) {
            self.0.lock().unwrap().notify_backtrack(n);
        }
        fn propagate(&mut self) -> i32 {
            self.0.lock().unwrap().propagate()
        }
        fn add_reason_clause_lit(&mut self, l: i32) -> i32 {
            self.0.lock().unwrap().add_reason_clause_lit(l)
        }
        fn check_found_model(&mut self, m: &[i32]) -> bool {
            self.0.lock().unwrap().check_found_model(m)
        }
    }

    let n = 6;
    let gs = color_swap_generator_k6();
    let sym = Arc::new(Mutex::new(SymmetryPropagator::new(gs)));
    let observed = sym.lock().unwrap().observed_vars();

    let mut solver = Solver::new();
    feed_clauses(&mut solver, &r33_triangle_bans(n));
    solver.connect_propagator(
        Box::new(Shim(sym.clone())) as Box<dyn ExternalPropagator>,
        &observed,
    );
    let verdict = solver.solve();
    assert_eq!(verdict, SolveResult::Unsat);

    let stats = sym.lock().unwrap().stats.clone();
    // Color-swap on R(3,3)/K_6 should fire at least once — the first
    // time CaDiCaL sets v1=True, the comparator violates.
    // The exact count depends on CaDiCaL's branching; we just require
    // >0 to prove the propagator was reached.
    assert!(
        stats.violations_by_gen[0] > 0 || stats.conflicts_emitted > 0,
        "expected sym propagator to fire: stats={:?}", stats
    );
}
