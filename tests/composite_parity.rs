//! End-to-end parity test for PR-1 (CompositePropagator).
//!
//! Claim under test: wrapping a single `BicliquePropagator` in a
//! `CompositePropagator` is behaviorally identical to using the
//! `BicliquePropagator` directly — same verdict, same conflict count.
//!
//! Instance: R(3,3)/K_6 with triangle ban clauses in the CNF. The
//! propagator's ban-group constraints are therefore redundant with the
//! CNF (as in the v0.5 certified pipeline, where SBP+card+chain live in
//! the CNF and the propagator supplements with ban-group propagation).
//!
//! We don't pin exact conflict counts — CaDiCaL tuning can drift.
//! We pin (a) the verdict (UNSAT) and (b) bit-exact parity between paths.

use cascade::biclique;
use cascade::cadical::{ExternalPropagator, Solver, SolveResult};
use cascade::cardinality::ev;
use cascade::propagator::{BicliquePropagator, CompositePropagator};

/// Generate triangle ban clauses for R(3,3)/K_n: for every triangle
/// {a,b,c} (a<b<c in 1..=n), add `(¬ab ∨ ¬ac ∨ ¬bc)` (red ban) and
/// `(ab ∨ ac ∨ bc)` (blue ban).
fn r33_triangle_bans(n: u32) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    for a in 1..=n {
        for b in (a + 1)..=n {
            for c in (b + 1)..=n {
                let e_ab = ev(a, b, n).raw();
                let e_ac = ev(a, c, n).raw();
                let e_bc = ev(b, c, n).raw();
                out.push(vec![-e_ab, -e_ac, -e_bc]); // red ban
                out.push(vec![e_ab, e_ac, e_bc]);    // blue ban
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

fn run_r33_k6_bare() -> (SolveResult, i64) {
    let n = 6;
    let decomp = biclique::decompose(n, 3, 3);
    let observed: Vec<i32> = (1..=decomp.n_edges as i32).collect();
    let prop = BicliquePropagator::new(decomp);

    let mut solver = Solver::new();
    feed_clauses(&mut solver, &r33_triangle_bans(n));
    solver.connect_propagator(Box::new(prop) as Box<dyn ExternalPropagator>, &observed);
    let verdict = solver.solve();
    let conflicts = solver.conflicts();
    (verdict, conflicts)
}

fn run_r33_k6_via_composite() -> (SolveResult, i64) {
    let n = 6;
    let decomp = biclique::decompose(n, 3, 3);
    let observed: Vec<i32> = (1..=decomp.n_edges as i32).collect();
    let inner = BicliquePropagator::new(decomp);

    let mut comp = CompositePropagator::new();
    comp.push(Box::new(inner));

    let mut solver = Solver::new();
    feed_clauses(&mut solver, &r33_triangle_bans(n));
    solver.connect_propagator(Box::new(comp) as Box<dyn ExternalPropagator>, &observed);
    let verdict = solver.solve();
    let conflicts = solver.conflicts();
    (verdict, conflicts)
}

#[test]
fn r33_k6_bare_is_unsat() {
    let (verdict, conflicts) = run_r33_k6_bare();
    assert_eq!(verdict, SolveResult::Unsat, "bare propagator path");
    println!("bare: {} conflicts", conflicts);
}

#[test]
fn r33_k6_composite_one_sub_is_unsat() {
    let (verdict, conflicts) = run_r33_k6_via_composite();
    assert_eq!(verdict, SolveResult::Unsat, "composite path");
    println!("composite: {} conflicts", conflicts);
}

#[test]
fn r33_k6_bare_and_composite_match() {
    let (bare_verdict, bare_conf) = run_r33_k6_bare();
    let (comp_verdict, comp_conf) = run_r33_k6_via_composite();

    assert_eq!(bare_verdict, comp_verdict, "verdict mismatch");
    assert_eq!(
        bare_conf, comp_conf,
        "conflict count diverged: bare={}, composite={}",
        bare_conf, comp_conf
    );
    println!("parity ok: {} conflicts both paths", bare_conf);
}
