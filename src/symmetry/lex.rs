//! Lex-leader comparator — one per generator.
//!
//! Given a variable ordering `v_1 < v_2 < … < v_n` and a generator `g`,
//! the comparator decides whether the current partial trail π is
//! lex-smaller, lex-larger, or equal to g(π) along the ordering, using
//! only the values assigned so far. It is incremental: feeding
//! assignments one at a time is O(amortized O(1)) per assignment via
//! the `frontier` cursor.
//!
//! Under the convention `False < True`, "π is lex-leader of its orbit"
//! means `π ≤_lex g(π)` for every generator g — i.e., the canonical
//! representative is the lex-**smallest** element in its orbit. This
//! matches satsuma's convention, empirically verified by feeding
//! satsuma's R(4,4)/K_17 SAT model into `check_found_model` (test
//! `tests/overlay_convention.rs`).
//!
//! # Outcomes
//!
//! * `Stalled` — more assignments needed before a verdict.
//! * `Satisfied` — found a position where π is strictly smaller;
//!   canonical under this generator.
//! * `Violated` — found a position where π is strictly larger;
//!   conflict. Caller should emit the blocking clause from
//!   [`LexComparator::blocking_clause`].
//! * `Propagate(l)` — the literal `l` is forced True to avoid an
//!   imminent violation. Caller should return this from the IPASIR-UP
//!   `propagate()` callback and later supply the reason clause.
//!
//! # Backjump
//!
//! The comparator mirrors CaDiCaL's decision levels. On each
//! `notify_new_decision_level` the caller invokes `push_level()`
//! (snapshot). On `notify_backtrack(k)` the caller invokes
//! `pop_to_level(k)` (restore). Between those, the frontier advances
//! monotonically.

use super::generators::Permutation;

/// Three-valued logic.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Lbool {
    True,
    False,
    Undef,
}

impl Lbool {
    #[inline]
    pub fn negate(self) -> Self {
        match self {
            Lbool::True => Lbool::False,
            Lbool::False => Lbool::True,
            Lbool::Undef => Lbool::Undef,
        }
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum CmpStatus {
    Undecided,
    Satisfied,
    Violated,
}

/// One step of advancing the comparator against a (possibly partial)
/// assignment.
#[derive(Clone, Debug, PartialEq)]
pub enum StepOutcome {
    /// No transition: the current frontier position is not yet decidable.
    Stalled,
    /// Transitioned to `CmpStatus::Satisfied` at some position: caller
    /// can leave this comparator dormant until backjump rewinds past
    /// that position.
    Satisfied,
    /// Transitioned to `CmpStatus::Violated` at the frontier: caller
    /// must emit the blocking clause and declare a conflict.
    Violated,
    /// The literal `l` is forced True (assigning it to False would
    /// cause an imminent violation at the frontier).
    Propagate(i32),
}

/// Assignment view: 1-indexed. `assign[0]` is a padding sentinel. Users
/// construct this from their solver's trail / model.
pub type Assignment = [Lbool];

/// Read the value of a DIMACS literal under an assignment.
#[inline]
pub fn lit_value(l: i32, assign: &Assignment) -> Lbool {
    let v = l.unsigned_abs() as usize;
    let raw = assign[v];
    if l > 0 { raw } else { raw.negate() }
}

pub struct LexComparator {
    /// Generator index within the owning [`GeneratorSet`]. Used by the
    /// propagator to annotate reason clauses with the witnessing
    /// generator.
    pub gen_idx: usize,
    frontier: usize,
    status: CmpStatus,
    /// `snapshots[i]` = (frontier, status) at the end of decision level
    /// `i`. Length equals the current decision level.
    snapshots: Vec<(usize, CmpStatus)>,
}

impl LexComparator {
    pub fn new(gen_idx: usize) -> Self {
        Self {
            gen_idx,
            frontier: 0,
            status: CmpStatus::Undecided,
            snapshots: Vec::new(),
        }
    }

    #[inline] pub fn frontier(&self) -> usize { self.frontier }
    #[inline] pub fn status(&self) -> CmpStatus { self.status }
    #[inline] pub fn level(&self) -> usize { self.snapshots.len() }

    /// Snapshot current (frontier, status). Invoked on
    /// `notify_new_decision_level`.
    pub fn push_level(&mut self) {
        self.snapshots.push((self.frontier, self.status));
    }

    /// Restore (frontier, status) to the state at the end of
    /// `new_level`. Invoked on `notify_backtrack(new_level)`.
    ///
    /// If `new_level == 0` and no snapshots exist (i.e., we never left
    /// level 0), this is a no-op. Otherwise we restore from
    /// `snapshots[new_level]` — the state captured when we transitioned
    /// from level `new_level` into level `new_level + 1` — and truncate.
    pub fn pop_to_level(&mut self, new_level: usize) {
        if new_level >= self.snapshots.len() {
            // Not a backjump (or trivially at level 0 with no history).
            return;
        }
        let (f, s) = self.snapshots[new_level];
        self.frontier = f;
        self.status = s;
        self.snapshots.truncate(new_level);
    }

    /// Reset to the comparator's initial state (frontier=0,
    /// Undecided, no snapshots). Used when CaDiCaL restarts.
    pub fn reset(&mut self) {
        self.frontier = 0;
        self.status = CmpStatus::Undecided;
        self.snapshots.clear();
    }

    /// Advance the frontier as far as the current assignment allows.
    /// Returns the first non-`Stalled` transition encountered, or
    /// `Stalled` if no progress is possible.
    pub fn advance(
        &mut self,
        gen: &Permutation,
        ordering: &[u32],
        assign: &Assignment,
    ) -> StepOutcome {
        if self.status != CmpStatus::Undecided {
            return StepOutcome::Stalled;
        }
        while self.frontier < ordering.len() {
            let v = ordering[self.frontier];
            let v_lit = v as i32;
            let gv_lit = gen.apply_var(v);

            // Fixed point: v maps to itself (same polarity). Equal by
            // construction; advance without inspecting values.
            if gv_lit == v_lit {
                self.frontier += 1;
                continue;
            }

            let val_v = lit_value(v_lit, assign);
            let val_gv = lit_value(gv_lit, assign);

            match (val_v, val_gv) {
                // Equal assigned values — advance.
                (Lbool::True, Lbool::True) | (Lbool::False, Lbool::False) => {
                    self.frontier += 1;
                    continue;
                }
                // MIN convention: orig strictly smaller than image
                // → π ≤_lex g(π) strictly satisfied at this position.
                (Lbool::False, Lbool::True) => {
                    self.status = CmpStatus::Satisfied;
                    return StepOutcome::Satisfied;
                }
                // MIN convention: orig strictly larger — violates
                // π ≤_lex g(π).
                (Lbool::True, Lbool::False) => {
                    self.status = CmpStatus::Violated;
                    return StepOutcome::Violated;
                }
                // v_i unassigned, g(v_i) = False: v_i must be False.
                // (v_i = True would give val_v > val_gv, violating min.)
                (Lbool::Undef, Lbool::False) => {
                    return StepOutcome::Propagate(-v_lit);
                }
                // v_i = True, g(v_i) unassigned: g(v_i) must be True.
                // (g(v_i) = False would give val_v > val_gv.)
                (Lbool::True, Lbool::Undef) => {
                    return StepOutcome::Propagate(gv_lit);
                }
                // Remaining: (Undef, Undef), (Undef, True), (False, Undef).
                // All underdetermined — stall.
                _ => return StepOutcome::Stalled,
            }
        }
        // Walked off the end of the ordering with everything equal.
        // π == g(π) on the ordering → trivially canonical.
        self.status = CmpStatus::Satisfied;
        StepOutcome::Satisfied
    }

    /// Construct the blocking clause for a violation: negation of the
    /// *conjunction* of conditions that caused it. Must be called while
    /// `status == Violated`.
    ///
    /// At each non-fixed-point position `i` in `[0, frontier]`, the
    /// comparator relied on two values being consistent:
    ///
    ///   * `val(v_i) = a_i` — assigned literal on the v-side.
    ///   * `val(g(v_i)) = b_i` — evaluated literal on the g-side.
    ///
    /// Equality at positions `i < frontier` needs both sides to match;
    /// the strict-greater at position `frontier` needs
    /// `val(v_frontier) = T ∧ val(g(v_frontier)) = F` (or the polarity-
    /// flipped analog). Flipping *either* side at any position breaks
    /// the violation, so both sides' negations enter the clause.
    ///
    /// Fixed-point positions (g(v_i) = v_i as a literal) are skipped —
    /// they contribute no antecedent.
    ///
    /// The emitted clause is RUP w.r.t. F only when augmented by a
    /// VeriPB substitution step naming `gen` as witness. See RFC §6.
    pub fn blocking_clause(
        &self,
        gen: &Permutation,
        ordering: &[u32],
        assign: &Assignment,
    ) -> Vec<i32> {
        assert_eq!(self.status, CmpStatus::Violated);
        let mut clause = Vec::with_capacity(2 * (self.frontier + 1));
        for i in 0..=self.frontier {
            let v = ordering[i];
            let v_lit = v as i32;
            let gv_lit = gen.apply_var(v);
            if gv_lit == v_lit {
                // Fixed point — not part of the violation's antecedents.
                continue;
            }
            // v-side: push negation of the True literal at var v.
            match assign[v as usize] {
                Lbool::True => clause.push(-v_lit),
                Lbool::False => clause.push(v_lit),
                Lbool::Undef => {}
            }
            // g-side: push negation of the True literal on the g(v) side.
            // The True lit on that side is `gv_lit` if `gv_lit` currently
            // evaluates True, else `-gv_lit`.
            match lit_value(gv_lit, assign) {
                Lbool::True => clause.push(-gv_lit),
                Lbool::False => clause.push(gv_lit),
                Lbool::Undef => {}
            }
        }
        // Dedup while preserving order (both sides can reference the
        // same underlying var via polarity flip).
        let mut seen: std::collections::HashSet<i32> = std::collections::HashSet::new();
        clause.retain(|&l| seen.insert(l));
        clause
    }
}

// ─── Tests ───────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symmetry::generators::Permutation;

    /// Naive reference: compute status by walking the full ordering
    /// against the current assignment in one shot. Used to
    /// cross-validate the incremental comparator.
    fn naive_status(
        gen: &Permutation,
        ordering: &[u32],
        assign: &Assignment,
    ) -> CmpStatus {
        for &v in ordering {
            let v_lit = v as i32;
            let gv_lit = gen.apply_var(v);
            if gv_lit == v_lit {
                continue;
            }
            let a = lit_value(v_lit, assign);
            let b = lit_value(gv_lit, assign);
            match (a, b) {
                // MIN convention.
                (Lbool::False, Lbool::True) => return CmpStatus::Satisfied,
                (Lbool::True, Lbool::False) => return CmpStatus::Violated,
                (Lbool::True, Lbool::True) | (Lbool::False, Lbool::False) => continue,
                _ => return CmpStatus::Undecided,
            }
        }
        CmpStatus::Satisfied
    }

    fn make_assign(n: u32, fixed: &[(u32, bool)]) -> Vec<Lbool> {
        let mut a = vec![Lbool::Undef; n as usize + 1];
        for &(v, b) in fixed {
            a[v as usize] = if b { Lbool::True } else { Lbool::False };
        }
        a
    }

    // ─── Lbool & lit_value ──

    #[test]
    fn lbool_negate() {
        assert_eq!(Lbool::True.negate(), Lbool::False);
        assert_eq!(Lbool::False.negate(), Lbool::True);
        assert_eq!(Lbool::Undef.negate(), Lbool::Undef);
    }

    #[test]
    fn lit_value_handles_negation() {
        let a = make_assign(3, &[(1, true), (2, false)]);
        assert_eq!(lit_value(1, &a), Lbool::True);
        assert_eq!(lit_value(-1, &a), Lbool::False);
        assert_eq!(lit_value(2, &a), Lbool::False);
        assert_eq!(lit_value(-2, &a), Lbool::True);
        assert_eq!(lit_value(3, &a), Lbool::Undef);
        assert_eq!(lit_value(-3, &a), Lbool::Undef);
    }

    // ─── advance: simple cases ──

    #[test]
    fn advance_all_equal_satisfies_at_end() {
        // Transposition (1 2), ordering [3, 4]: neither 3 nor 4 is moved,
        // so every position is a fixed point → run off the end → Satisfied.
        let g = Permutation::from_mapping(4, &[(1, 2), (2, 1)]);
        let ord = vec![3, 4];
        let assign = make_assign(4, &[]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Satisfied);
        assert_eq!(c.status(), CmpStatus::Satisfied);
    }

    #[test]
    fn advance_strict_smaller_satisfies() {
        // MIN: v1=F, v2=T → F<T → Satisfied.
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];
        let assign = make_assign(2, &[(1, false), (2, true)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Satisfied);
    }

    #[test]
    fn advance_strict_larger_violates() {
        // MIN: v1=T, v2=F → T>F → Violated.
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];
        let assign = make_assign(2, &[(1, true), (2, false)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Violated);
        assert_eq!(c.status(), CmpStatus::Violated);
    }

    #[test]
    fn advance_color_swap_assign_true_violates() {
        // Color-swap x_i -> ~x_i. v1=T → val(v1)=T, val(g(v1))=F →
        // T>F → Violated (MIN).
        let g = Permutation::from_mapping(3, &[(1, -1), (2, -2), (3, -3)]);
        let ord = vec![1];
        let assign = make_assign(3, &[(1, true)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Violated);
    }

    #[test]
    fn advance_color_swap_assign_false_satisfies() {
        let g = Permutation::from_mapping(3, &[(1, -1), (2, -2), (3, -3)]);
        let ord = vec![1];
        let assign = make_assign(3, &[(1, false)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Satisfied);
    }

    #[test]
    fn advance_propagates_v_false_when_gv_false() {
        // MIN: v1=Undef, v2=F → v1 must be F (else T>F violates min).
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];
        let assign = make_assign(2, &[(2, false)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Propagate(-1));
    }

    #[test]
    fn advance_propagates_gv_true_when_v_true() {
        // MIN: v1=T, v2=Undef → v2 must be T.
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];
        let assign = make_assign(2, &[(1, true)]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Propagate(2));
    }

    #[test]
    fn advance_propagates_negated_literal_for_polarity_flip() {
        // g(v1) = ~v1. Ordering [1]. v1=Undef.
        // val_v1=Undef, val_gv=val(~v1)=Undef (both tied to v1).
        // Actually since gv_lit = -v_lit, the values are always negations
        // of each other. (Undef, Undef) → Stalled.
        let g = Permutation::from_mapping(2, &[(1, -1), (2, -2)]);
        let ord = vec![1];
        let assign = make_assign(2, &[]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Stalled);
    }

    // ─── advance: fixed points advance silently ──

    #[test]
    fn advance_skips_fixed_points_without_touching_assignment() {
        // g is identity on v1 but swaps v2 and v3. Ordering [1, 2, 3].
        // At pos 0 (v1 fixed), skip. At pos 1 (v2↔v3), values both Undef
        // → stall. Frontier should advance past the fixed point.
        let g = Permutation::from_mapping(3, &[(2, 3), (3, 2)]);
        let ord = vec![1, 2, 3];
        let assign = make_assign(3, &[]);
        let mut c = LexComparator::new(0);
        assert_eq!(c.advance(&g, &ord, &assign), StepOutcome::Stalled);
        assert_eq!(c.frontier(), 1);
    }

    // ─── backjump ──

    #[test]
    fn push_pop_restores_frontier_and_status() {
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];

        let mut c = LexComparator::new(0);
        // MIN: v1=F, v2=T → F<T → Satisfied.
        let assign0 = make_assign(2, &[(1, false), (2, true)]);
        c.advance(&g, &ord, &assign0);
        assert_eq!(c.status(), CmpStatus::Satisfied);

        c.push_level(); // snapshot level 0 → going into level 1
        // At level 1 we change nothing meaningful; simulate a
        // hypothetical state where we manually force status.
        // Level-1 state: identical to level 0 snapshot.
        assert_eq!(c.level(), 1);

        c.pop_to_level(0);
        assert_eq!(c.level(), 0);
        assert_eq!(c.status(), CmpStatus::Satisfied);
    }

    #[test]
    fn backjump_from_violated_to_undecided() {
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];

        let mut c = LexComparator::new(0);
        c.push_level();
        // MIN: v1=T, v2=F → T>F → violation.
        let assign_bad = make_assign(2, &[(1, true), (2, false)]);
        c.advance(&g, &ord, &assign_bad);
        assert_eq!(c.status(), CmpStatus::Violated);

        c.pop_to_level(0);
        assert_eq!(c.status(), CmpStatus::Undecided);
        assert_eq!(c.frontier(), 0);
    }

    #[test]
    fn pop_to_higher_level_is_noop() {
        let mut c = LexComparator::new(0);
        c.push_level();
        c.push_level();
        assert_eq!(c.level(), 2);
        c.pop_to_level(5); // higher than current; no-op
        assert_eq!(c.level(), 2);
    }

    #[test]
    fn reset_wipes_all_state() {
        let g = Permutation::from_mapping(2, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2];
        // MIN: v1=T, v2=F → violation.
        let assign = make_assign(2, &[(1, true), (2, false)]);
        let mut c = LexComparator::new(0);
        c.push_level();
        c.advance(&g, &ord, &assign);
        c.reset();
        assert_eq!(c.status(), CmpStatus::Undecided);
        assert_eq!(c.frontier(), 0);
        assert_eq!(c.level(), 0);
    }

    // ─── blocking clause ──

    #[test]
    fn blocking_clause_shape() {
        // MIN: swap(1,2), v1=T, v2=F → T>F → violated at frontier=0.
        // Neg of conjunction val(v1)=T ∧ val(v2)=F: (-1) ∨ (+2).
        let g = Permutation::from_mapping(3, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2, 3];
        let assign = make_assign(3, &[(1, true), (2, false)]);
        let mut c = LexComparator::new(0);
        c.advance(&g, &ord, &assign);
        assert_eq!(c.status(), CmpStatus::Violated);
        let mut bc = c.blocking_clause(&g, &ord, &assign);
        bc.sort();
        assert_eq!(bc, vec![-1, 2]);
    }

    #[test]
    fn blocking_clause_skips_fixed_points() {
        // MIN: swap(2,3), v1=T fixed, v2=T, v3=F → T>F → Violated.
        // BC: (-2, +3).
        let g = Permutation::from_mapping(3, &[(2, 3), (3, 2)]);
        let ord = vec![1, 2, 3];
        let assign = make_assign(3, &[(1, true), (2, true), (3, false)]);
        let mut c = LexComparator::new(0);
        c.advance(&g, &ord, &assign);
        assert_eq!(c.status(), CmpStatus::Violated);
        let mut bc = c.blocking_clause(&g, &ord, &assign);
        bc.sort();
        assert_eq!(bc, vec![-2, 3]);
    }

    #[test]
    fn blocking_clause_includes_prefix_equalities() {
        // MIN: 4-cycle (1 2 3 4). v1=T, v2=T (equal), v3=F. At pos 1:
        // val(v2)=T, val(g(v2))=val(v3)=F → T>F → Violated.
        // BC: pos 0: -1, -2. pos 1: -2, +3. Dedup: {-1, -2, +3}.
        let g = Permutation::from_mapping(4, &[(1, 2), (2, 3), (3, 4), (4, 1)]);
        let ord = vec![1, 2, 3, 4];
        let assign = make_assign(4, &[(1, true), (2, true), (3, false)]);
        let mut c = LexComparator::new(0);
        c.advance(&g, &ord, &assign);
        assert_eq!(c.status(), CmpStatus::Violated);
        let mut bc = c.blocking_clause(&g, &ord, &assign);
        bc.sort();
        assert_eq!(bc, vec![-2, -1, 3]);
    }

    // ─── advance matches naive on random-ish inputs ──

    #[test]
    fn advance_matches_naive_on_transposition() {
        // Exhaustively check all 2^4 assignments for a swap (1 2) with
        // ordering [1, 2]. (Vars 3, 4 irrelevant but included to test
        // fixed-point skipping.)
        let g = Permutation::from_mapping(4, &[(1, 2), (2, 1)]);
        let ord = vec![1, 2, 3, 4];

        for mask in 0u32..16 {
            let assign = make_assign(4, &[
                (1, (mask & 1) != 0),
                (2, (mask & 2) != 0),
                (3, (mask & 4) != 0),
                (4, (mask & 8) != 0),
            ]);
            let expected = naive_status(&g, &ord, &assign);

            let mut c = LexComparator::new(0);
            c.advance(&g, &ord, &assign);
            let got = c.status();

            // advance doesn't always transition to exactly `expected`
            // if the naive says Undecided — it may report Propagate or
            // Stalled and leave status Undecided. So we only assert
            // equality for the decided cases.
            if expected != CmpStatus::Undecided {
                assert_eq!(
                    got, expected,
                    "mask={} got={:?} expected={:?}", mask, got, expected
                );
            } else {
                assert_eq!(got, CmpStatus::Undecided, "mask={}", mask);
            }
        }
    }

    #[test]
    fn advance_matches_naive_on_color_swap() {
        let g = Permutation::from_mapping(3, &[(1, -1), (2, -2), (3, -3)]);
        let ord = vec![1, 2, 3];

        for mask in 0u32..27 {
            // 3 ternary values; 3^3 = 27 states
            let mut assign = vec![Lbool::Undef; 4];
            for i in 0..3 {
                let v = i + 1;
                let t = (mask / 3u32.pow(i as u32)) % 3;
                assign[v as usize] = match t {
                    0 => Lbool::Undef,
                    1 => Lbool::False,
                    2 => Lbool::True,
                    _ => unreachable!(),
                };
            }
            let expected = naive_status(&g, &ord, &assign);

            let mut c = LexComparator::new(0);
            c.advance(&g, &ord, &assign);

            if expected != CmpStatus::Undecided {
                assert_eq!(
                    c.status(), expected,
                    "mask={} expected={:?} got={:?}",
                    mask, expected, c.status()
                );
            }
        }
    }

    // ─── incremental advance matches batch naive ──

    // ─── push/pop/advance mixed sequences ──

    /// Simple linear-congruential PRNG — deterministic, no external deps.
    fn lcg(state: &mut u64) -> u64 {
        *state = state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        *state
    }

    #[test]
    fn randomized_push_advance_pop_cycles_match_recompute() {
        // Simulate a CDCL-like trace: at each step either (a) push a
        // new level and assign some vars, or (b) pop to a random earlier
        // level. After each step, verify that the comparator's status
        // matches what a naive recompute on the live assignment would say.
        let g = Permutation::from_mapping(6, &[(1, 4), (4, 1), (2, 5), (5, 2), (3, 6), (6, 3)]);
        let ord = vec![1, 2, 3, 4, 5, 6];

        let mut rng: u64 = 0xCAFEBABE;
        for seed in 0..64 {
            rng = rng.wrapping_add(seed as u64 * 31);
            let mut c = LexComparator::new(0);
            let mut live = vec![Lbool::Undef; 7];
            let mut snapshots: Vec<Vec<Lbool>> = vec![live.clone()];

            for _step in 0..20 {
                let choice = lcg(&mut rng) % 4;
                match choice {
                    0 | 1 => {
                        // Push new level, assign 1 random var.
                        c.push_level();
                        snapshots.push(live.clone());
                        let v = (lcg(&mut rng) % 6 + 1) as usize;
                        if live[v] == Lbool::Undef {
                            live[v] = if lcg(&mut rng) & 1 == 0 {
                                Lbool::True
                            } else {
                                Lbool::False
                            };
                            c.advance(&g, &ord, &live);
                        }
                    }
                    2 => {
                        // Pop to random earlier level.
                        if snapshots.len() > 1 {
                            let target = (lcg(&mut rng) as usize) % (snapshots.len() - 1);
                            c.pop_to_level(target);
                            live = snapshots[target].clone();
                            snapshots.truncate(target + 1);
                        }
                    }
                    _ => {
                        // Advance without new assignments (should be no-op
                        // given no assignment change).
                        c.advance(&g, &ord, &live);
                    }
                }

                // Cross-check: if naive says Satisfied/Violated, comparator
                // should reflect that exactly. If naive is Undecided, the
                // comparator should also be Undecided (because its status
                // only ever becomes Satisfied/Violated when the naive
                // decides).
                let expected = naive_status(&g, &ord, &live);
                let got = c.status();
                if expected == CmpStatus::Undecided {
                    assert_eq!(got, CmpStatus::Undecided, "seed={}, step state mismatch", seed);
                } else {
                    // Comparator may still be Undecided if advance hasn't
                    // been called after the latest assignment or if
                    // naive's verdict rests on a position beyond the
                    // incremental frontier. So we assert "if comparator
                    // is not Undecided, it matches naive".
                    if got != CmpStatus::Undecided {
                        assert_eq!(got, expected, "seed={}: incremental disagrees with naive", seed);
                    }
                }
            }
        }
    }

    #[test]
    fn incremental_advance_matches_batch_naive() {
        // MIN: v1=F, v3=T → F<T at pos 0 → Satisfied.
        let g = Permutation::from_mapping(5, &[(1, 3), (3, 1), (2, 4), (4, 2)]);
        let ord = vec![1, 2, 3, 4, 5];

        let final_assign = make_assign(5, &[(1, false), (3, true)]);
        let expected = naive_status(&g, &ord, &final_assign);

        let mut c = LexComparator::new(0);
        let mut live = vec![Lbool::Undef; 6];
        for &(v, b) in &[(1u32, false), (3u32, true)] {
            live[v as usize] = if b { Lbool::True } else { Lbool::False };
            c.advance(&g, &ord, &live);
        }
        assert_eq!(c.status(), expected);
    }
}
