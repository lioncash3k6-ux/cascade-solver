//! Online symmetry propagator — IPASIR-UP driver for LexComparators.
//!
//! This is the integration layer between CaDiCaL's external-propagator
//! callbacks and the [`LexComparator`] per-generator state machines.
//! It owns:
//!
//!   * a [`GeneratorSet`] from satsuma (or any other source);
//!   * one [`LexComparator`] per generator;
//!   * a mirror of the solver's variable assignment;
//!   * a trail + level-boundary stack for backjump;
//!   * a pending-conflict queue drained by `propagate()`.
//!
//! # Scope in v0.6 (PR-4)
//!
//! Violations only. When a comparator's `advance()` returns
//! `StepOutcome::Violated`, we build a blocking clause (negation of the
//! trail prefix) and enqueue it as a "conflict-by-propagation": on the
//! next `propagate()` call we return the propagated literal (which is
//! already assigned to the opposite value), CaDiCaL detects the
//! contradiction, asks for the reason via `add_reason_clause_lit`, and
//! runs conflict analysis on the blocking clause as its reason.
//!
//! `StepOutcome::Propagate(...)` outcomes are ignored in PR-4: the
//! comparator will re-detect the violation once the solver commits the
//! "wrong" assignment, at which point we emit the blocking clause. The
//! cost is one extra decision per would-be propagation; the benefit is
//! a much simpler, less error-prone implementation for the first cut.
//!
//! # Soundness note
//!
//! Blocking clauses are NOT RUP against the bare CNF — they are only
//! sound w.r.t. VeriPB substitution witnesses naming the violating
//! generator. PR-4 is therefore only correct under `--online-sym=on`
//! *without* `--certified`. PR-5 will wire the VeriPB `red` emission.

use crate::cadical::ExternalPropagator;
use crate::symmetry::generators::{GeneratorSet, Permutation};
use crate::symmetry::lex::{lit_value, CmpStatus, Lbool, LexComparator, StepOutcome};
use crate::symmetry::proof::SymProofLog;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

/// A queued conflict ready to be surfaced to CaDiCaL.
#[derive(Clone, Debug)]
struct PendingConflict {
    /// The "propagated" literal we return from `propagate()`. It is
    /// already assigned to the opposite value; CaDiCaL treats this as a
    /// conflict and asks for the reason.
    lit: i32,
    /// The reason/blocking clause with `lit` first.
    clause: Vec<i32>,
    /// Which generator witnessed the violation. Used in PR-5 for proof
    /// emission.
    #[allow(dead_code)]
    gen_idx: usize,
}

pub struct SymmetryPropagator {
    gen_set: GeneratorSet,
    ordering: Vec<u32>,
    comparators: Vec<LexComparator>,
    /// When false, `StepOutcome::Propagate(_)` is silently dropped —
    /// the propagator only surfaces violations (PR-4 behavior). Default
    /// true; set via [`SymmetryPropagator::set_propagation_enabled`] or
    /// the `CASCADE_SYM_NO_PROPAGATE` env var at construction time.
    propagation_enabled: bool,
    /// When false, `StepOutcome::Violated` is silently dropped — the
    /// propagator only surfaces propagations. Default true; set via
    /// `CASCADE_SYM_NO_VIOLATIONS=1` env var at construction time.
    violations_enabled: bool,
    /// Optional proof log. When present (PR-5 `--certified` mode),
    /// every blocking/propagation clause is logged with its witnessing
    /// generator index for later VeriPB `red` emission.
    proof_log: Option<Arc<Mutex<SymProofLog>>>,

    /// Learned-clause orbit closure (RFC-0002, SOUND version).
    /// When > 0, each CDCL-learned clause is orbit-closed by applying
    /// `learned_orbit_k` random group elements and injecting the images
    /// as external clauses. This IS sound because learned clauses are
    /// logical consequences of F, and h(learned) is also a logical
    /// consequence for any h ∈ Aut(F).
    /// Controlled by `CASCADE_SYM_LEARNED_ORBIT_K` env var (default 0).
    learned_orbit_k: usize,
    /// Buffer for the currently-streaming learned clause.
    learned_buf: Vec<i32>,
    /// External clauses waiting to be injected via cb_has_external_clause.
    external_queue: Vec<Vec<i32>>,
    external_cursor: usize,
    external_lit_cursor: usize,
    /// RNG state for random group element generation.
    orbit_rng: u64,
    /// Orbit-closed clause learning cap (RFC-0002). When > 0, every
    /// blocking/propagation clause our propagator emits is amplified
    /// by computing its images under the first `orbit_closure_k`
    /// generators and enqueuing each. Each image is sound (same
    /// soundness argument as the original, with its own generator as
    /// witness). 0 disables. Controlled by `CASCADE_SYM_ORBIT_K` env
    /// var (default 0 for now — tune empirically per instance).
    orbit_closure_k: usize,

    /// Assignment mirror. Index 0 is padding; indices 1..=n_vars valid.
    assign: Vec<Lbool>,
    /// Trail of assigned vars (in order). Used for backjump.
    trail: Vec<u32>,
    /// Index into `trail` marking the start of each decision level.
    level_start: Vec<usize>,
    level: usize,

    pending: Vec<PendingConflict>,
    pending_head: usize,

    /// Reason clauses for propagated literals.
    reasons: HashMap<i32, Vec<i32>>,
    /// Cursor into each reason during add_reason_clause_lit serialization.
    reason_cursor: HashMap<i32, usize>,

    /// Stats for benchmarking.
    pub stats: Stats,
}

#[derive(Default, Debug, Clone)]
pub struct Stats {
    pub assignments_processed: u64,
    pub conflicts_emitted: u64,
    pub propagations_emitted: u64,
    pub orbit_images_emitted: u64,
    pub violations_by_gen: Vec<u64>,
    pub propagations_by_gen: Vec<u64>,
}

impl SymmetryPropagator {
    pub fn new(mut gen_set: GeneratorSet) -> Self {
        let ordering = if gen_set.ordering.is_empty() {
            (1..=gen_set.n_vars).collect()
        } else {
            gen_set.ordering.clone()
        };
        if std::env::var("CASCADE_SYM_INVERT_GENS")
            .map(|v| !v.is_empty() && v != "0")
            .unwrap_or(false)
        {
            gen_set.invert_all();
        }
        let comparators: Vec<_> = (0..gen_set.gens.len())
            .map(LexComparator::new)
            .collect();
        let n_gens = gen_set.gens.len();
        let n_vars = gen_set.n_vars;
        let propagation_enabled = std::env::var("CASCADE_SYM_NO_PROPAGATE")
            .map(|v| v.is_empty() || v == "0")
            .unwrap_or(true);
        let violations_enabled = std::env::var("CASCADE_SYM_NO_VIOLATIONS")
            .map(|v| v.is_empty() || v == "0")
            .unwrap_or(true);
        let orbit_closure_k: usize = std::env::var("CASCADE_SYM_ORBIT_K")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        let learned_orbit_k: usize = std::env::var("CASCADE_SYM_LEARNED_ORBIT_K")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(0);
        Self {
            gen_set,
            ordering,
            comparators,
            propagation_enabled,
            violations_enabled,
            proof_log: None,
            orbit_closure_k,
            learned_orbit_k,
            learned_buf: Vec::new(),
            external_queue: Vec::new(),
            external_cursor: 0,
            external_lit_cursor: 0,
            orbit_rng: 0xCAFE_BABE_DEAD_BEEF,
            assign: vec![Lbool::Undef; n_vars as usize + 1],
            trail: Vec::new(),
            level_start: Vec::new(),
            level: 0,
            pending: Vec::new(),
            pending_head: 0,
            reasons: HashMap::new(),
            reason_cursor: HashMap::new(),
            stats: Stats {
                violations_by_gen: vec![0; n_gens],
                propagations_by_gen: vec![0; n_gens],
                ..Default::default()
            },
        }
    }

    /// Runtime toggle for proactive propagation (PR-4b). When off, only
    /// violations are reported (PR-4 behavior).
    pub fn set_propagation_enabled(&mut self, enabled: bool) {
        self.propagation_enabled = enabled;
    }

    /// Attach a proof log (PR-5). When set, every blocking and
    /// propagation clause is recorded with the generator index that
    /// produced it, for later VeriPB `red` serialization.
    pub fn set_proof_log(&mut self, log: Arc<Mutex<SymProofLog>>) {
        self.proof_log = Some(log);
    }

    /// Read-only access to the generator set — used by main.rs when
    /// composing the final VeriPB proof.
    pub fn generators(&self) -> &[Permutation] {
        &self.gen_set.gens
    }

    /// Orbit-closed amplification — **FUNDAMENTALLY UNSOUND for
    /// lex-leader blocking clauses, DISABLED (orbit_closure_k=0).**
    ///
    /// The issue is NOT the VeriPB witness (conjugation h∘g_i∘h⁻¹ is
    /// correct algebraically). The issue is SEMANTIC: a blocking clause
    /// C prunes ONE non-canonical assignment from each orbit, leaving
    /// the lex-leader representative reachable. Applying a random group
    /// element h to C produces h(C), which may block the lex-leader
    /// itself — making the orbit entirely blocked → false UNSAT.
    ///
    /// Confirmed: R(4,4)/K_17 (SAT) returns false UNSAT at orbit_k≥10
    /// with both naive (commit 31920cb) AND conjugation-witness
    /// approaches. At orbit_k=5, random h's sometimes avoid the
    /// canonical rep (SAT returned, fewer conflicts) but this is
    /// probabilistic unsoundness.
    ///
    /// The ONLY safe orbit closure applies to CDCL-learned clauses
    /// (logical consequences of F, not redundancy rules). That requires
    /// CaDiCaL-internal access to the learned-clause callback, which
    /// IPASIR-UP doesn't expose.
    ///
    /// Infrastructure kept for potential future use with learned-clause
    /// interception.
    fn amplify_via_orbit(&mut self, source: &[i32], source_gen_idx: usize) {
        if self.orbit_closure_k == 0 {
            return;
        }
        let g_i = self.gen_set.gens[source_gen_idx].clone();
        let n_vars = self.gen_set.n_vars;
        let gens = self.gen_set.gens.clone();

        let mut seen: HashSet<Vec<i32>> = HashSet::new();
        seen.insert({
            let mut c = source.to_vec();
            c.sort();
            c
        });

        // RNG state for random walks.
        let mut rng: u64 = self.stats.orbit_images_emitted
            .wrapping_mul(6364136223846793005)
            .wrapping_add(source.len() as u64);

        for _ in 0..self.orbit_closure_k {
            // Generate random h by Cayley-graph walk (15 steps).
            let mut h = Permutation::identity(n_vars);
            for _ in 0..15 {
                rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                let idx = (rng >> 33) as usize % gens.len();
                let use_inv = (rng >> 16) & 1 == 1;
                let step = if use_inv { gens[idx].inverse() } else { gens[idx].clone() };
                h = step.compose(&h);
            }

            // Image clause = h(source).
            let image = h.apply_clause(source);
            let mut canon = image.clone();
            canon.sort();
            if !seen.insert(canon) {
                continue;
            }
            if image.is_empty() {
                continue;
            }

            // Filter by current assignment: all non-propagated lits
            // must be False for CaDiCaL to accept.
            let mut true_count = 0usize;
            let mut undef_lits: Vec<i32> = Vec::new();
            for &l in &image {
                match lit_value(l, &self.assign) {
                    Lbool::True => true_count += 1,
                    Lbool::Undef => undef_lits.push(l),
                    Lbool::False => {}
                }
            }
            if true_count > 0 {
                continue;
            }
            let propagated: i32 = match undef_lits.len() {
                0 => *image.last().unwrap(),
                1 => undef_lits[0],
                _ => continue,
            };

            // Sound VeriPB witness: h ∘ g_i ∘ h⁻¹ (conjugation).
            // We store the composed witness as a new Permutation and
            // add it to the proof log. For the gen_idx field in the
            // pending clause, we use source_gen_idx as a placeholder
            // (the actual witness is computed separately for proof
            // emission).
            let witness = h.compose(&g_i).compose(&h.inverse());

            let mut reason = vec![propagated];
            for &l in &image {
                if l != propagated {
                    reason.push(l);
                }
            }

            if let Some(log) = &self.proof_log {
                if let Ok(mut g) = log.lock() {
                    // Log with source_gen_idx; the actual witness permutation
                    // is the conjugate. For now store gen_idx as marker; the
                    // proof emitter can recompute the conjugate from the h.
                    g.push(image.clone(), source_gen_idx);
                }
            }

            self.pending.push(PendingConflict {
                lit: propagated,
                clause: reason,
                gen_idx: source_gen_idx,
            });
            self.stats.orbit_images_emitted += 1;
        }
    }

    /// All variables this propagator needs notifications for.
    pub fn observed_vars(&self) -> Vec<i32> {
        (1..=self.gen_set.n_vars as i32).collect()
    }

    pub fn n_generators(&self) -> usize {
        self.gen_set.gens.len()
    }

    /// Build a blocking clause for a comparator whose status is
    /// `Violated`. The clause has `propagated_lit` first (to match
    /// IPASIR-UP conventions for reason clauses) followed by the rest.
    fn build_blocking_clause(&self, comp_idx: usize) -> Vec<i32> {
        let c = &self.comparators[comp_idx];
        debug_assert_eq!(c.status(), CmpStatus::Violated);
        let gen = &self.gen_set.gens[c.gen_idx];
        c.blocking_clause(gen, &self.ordering, &self.assign)
    }

    /// Reason clause for a proactive propagation returned by
    /// `LexComparator::advance` as `StepOutcome::Propagate(lit)`.
    ///
    /// The propagation `lit` is forced because:
    ///   * positions `0..frontier` satisfied the lex-equality
    ///     `val(v_i) == val(g(v_i))`;
    ///   * at position `frontier`, either
    ///     `val(v_frontier)=T, val(g(v_frontier))=Undef` (forcing
    ///     `g(v_frontier)` True), or
    ///     `val(v_frontier)=Undef, val(g(v_frontier))=F` (forcing
    ///     `v_frontier` False).
    ///
    /// The resulting reason clause has `lit` first, followed by the
    /// negations of every literal on both sides of every equality step
    /// (both sides required for soundness — either flip would break the
    /// equality), plus the negation of the forcing literal at
    /// `frontier`.
    fn build_propagation_reason(
        &self,
        comp_idx: usize,
        propagated_lit: i32,
    ) -> Vec<i32> {
        let c = &self.comparators[comp_idx];
        let gen: &Permutation = &self.gen_set.gens[c.gen_idx];
        let frontier = c.frontier();

        let mut clause: Vec<i32> = Vec::with_capacity(2 * frontier + 2);
        clause.push(propagated_lit);

        // Equality antecedents at positions 0..frontier (strictly before
        // the forcing position). Each position contributes both sides.
        for i in 0..frontier {
            if i >= self.ordering.len() {
                break;
            }
            let v = self.ordering[i];
            let v_lit = v as i32;
            let gv_lit = gen.apply_var(v);
            if gv_lit == v_lit {
                // Fixed point — no antecedent at this position.
                continue;
            }
            match self.assign[v as usize] {
                Lbool::True => clause.push(-v_lit),
                Lbool::False => clause.push(v_lit),
                Lbool::Undef => {} // defensive; shouldn't happen in prefix
            }
            match lit_value(gv_lit, &self.assign) {
                Lbool::True => clause.push(-gv_lit),
                Lbool::False => clause.push(gv_lit),
                Lbool::Undef => {}
            }
        }

        // Forcing antecedent at position `frontier`.
        if frontier < self.ordering.len() {
            let v = self.ordering[frontier];
            let v_lit = v as i32;
            let gv_lit = gen.apply_var(v);
            // Classify the forcing case by looking at current values.
            let val_v = self.assign[v as usize];
            let val_gv = lit_value(gv_lit, &self.assign);
            match (val_v, val_gv) {
                // MIN: Propagate(-v): forcing was val(g(v))=F → True
                // side is -gv_lit; negate: gv_lit.
                (Lbool::Undef, Lbool::False) => clause.push(gv_lit),
                // MIN: Propagate(+gv_lit): forcing was val(v)=T →
                // True side is +v_lit; negate: -v_lit.
                (Lbool::True, Lbool::Undef) => clause.push(-v_lit),
                _ => {
                    // Stale propagation; propagate() will skip.
                }
            }
        }

        // Dedup while preserving order.
        let mut seen: HashSet<i32> = HashSet::new();
        clause.retain(|&l| seen.insert(l));
        clause
    }

    /// Walk every Undecided comparator once and enqueue any violation it
    /// reports.
    fn step_all_comparators(&mut self) {
        let n_gens = self.comparators.len();
        for idx in 0..n_gens {
            if self.comparators[idx].status() != CmpStatus::Undecided {
                continue;
            }
            // Loop because a single advance might only surface the next
            // decision, and there could be more Stalled→Satisfied
            // transitions in a single walk.
            loop {
                let gen = &self.gen_set.gens[self.comparators[idx].gen_idx];
                let outcome = self.comparators[idx].advance(gen, &self.ordering, &self.assign);
                match outcome {
                    StepOutcome::Stalled => break,
                    StepOutcome::Satisfied => break,
                    StepOutcome::Violated => {
                        self.stats.violations_by_gen[idx] += 1;
                        if !self.violations_enabled {
                            break;
                        }
                        let blocking = self.build_blocking_clause(idx);
                        if blocking.is_empty() {
                            break;
                        }
                        let gen_idx_for_log = self.comparators[idx].gen_idx;
                        if let Some(log) = &self.proof_log {
                            if let Ok(mut g) = log.lock() {
                                g.push(blocking.clone(), gen_idx_for_log);
                            }
                        }
                        let propagated = *blocking.last().unwrap();
                        let mut reason = vec![propagated];
                        for &l in &blocking {
                            if l != propagated {
                                reason.push(l);
                            }
                        }
                        self.pending.push(PendingConflict {
                            lit: propagated,
                            clause: reason,
                            gen_idx: idx,
                        });
                        // RFC-0002: orbit-closed amplification.
                        self.amplify_via_orbit(&blocking, gen_idx_for_log);
                        break;
                    }
                    StepOutcome::Propagate(lit) => {
                        if self.propagation_enabled {
                            self.stats.propagations_by_gen[idx] += 1;
                            let reason = self.build_propagation_reason(idx, lit);
                            let gen_idx_for_log = self.comparators[idx].gen_idx;
                            if let Some(log) = &self.proof_log {
                                if let Ok(mut g) = log.lock() {
                                    g.push(reason.clone(), gen_idx_for_log);
                                }
                            }
                            self.pending.push(PendingConflict {
                                lit,
                                clause: reason.clone(),
                                gen_idx: idx,
                            });
                            // RFC-0002: orbit-closed amplification.
                            self.amplify_via_orbit(&reason, gen_idx_for_log);
                        }
                        break;
                    }
                }
            }
        }
    }
}

impl ExternalPropagator for SymmetryPropagator {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for &l in lits {
            let v = l.unsigned_abs();
            if v == 0 || v > self.gen_set.n_vars {
                continue;
            }
            if self.assign[v as usize] != Lbool::Undef {
                // Reassignment — IPASIR-UP shouldn't send these but be
                // defensive.
                continue;
            }
            self.assign[v as usize] = if l > 0 { Lbool::True } else { Lbool::False };
            self.trail.push(v);
            self.stats.assignments_processed += 1;
        }
        self.step_all_comparators();
    }

    fn notify_new_decision_level(&mut self) {
        self.level += 1;
        self.level_start.push(self.trail.len());
        for c in &mut self.comparators {
            c.push_level();
        }
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        while self.level > new_level {
            if let Some(start) = self.level_start.pop() {
                while self.trail.len() > start {
                    let v = self.trail.pop().unwrap();
                    self.assign[v as usize] = Lbool::Undef;
                }
            }
            self.level -= 1;
        }
        for c in &mut self.comparators {
            c.pop_to_level(new_level);
        }
        // Discard pending + external queue — those were for a
        // now-unreachable trail state.
        self.pending.clear();
        self.pending_head = 0;
        self.external_queue.clear();
        self.external_cursor = 0;
        self.external_lit_cursor = 0;
    }

    fn propagate(&mut self) -> i32 {
        while self.pending_head < self.pending.len() {
            let i = self.pending_head;
            self.pending_head += 1;
            let conflict = &self.pending[i];

            // Sanity: the propagated lit should be False in the current
            // assignment (that's what makes it a conflict). If it's
            // True (e.g., re-propagated due to backjump + re-advance),
            // the conflict is stale — skip.
            let v = conflict.lit.unsigned_abs() as usize;
            let want = if conflict.lit > 0 { Lbool::True } else { Lbool::False };
            let cur = self.assign[v];
            if cur == want {
                // Already consistent; lose the pending conflict.
                continue;
            }
            // Register the reason and return. Distinguish propagation
            // (var currently Undef) from conflict (var assigned opposite).
            self.reasons.insert(conflict.lit, conflict.clause.clone());
            self.reason_cursor.insert(conflict.lit, 0);
            let lit = conflict.lit;
            if cur == Lbool::Undef {
                self.stats.propagations_emitted += 1;
            } else {
                self.stats.conflicts_emitted += 1;
            }
            return lit;
        }
        0
    }

    fn add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        let reason = match self.reasons.get(&propagated_lit) {
            Some(r) => r,
            None => return 0,
        };
        let cur = *self.reason_cursor.get(&propagated_lit).unwrap_or(&0);
        if cur < reason.len() {
            let lit = reason[cur];
            self.reason_cursor.insert(propagated_lit, cur + 1);
            lit
        } else {
            // Clause fully emitted; reset cursor so subsequent queries
            // (e.g., re-queries by CaDiCaL) re-serialize.
            self.reason_cursor.insert(propagated_lit, 0);
            0
        }
    }

    fn learning(&mut self, size: i32) -> bool {
        // Accept learned clauses of reasonable size for orbit closure.
        if self.learned_orbit_k == 0 {
            return false;
        }
        self.learned_buf.clear();
        size <= 50 // skip very large clauses — orbit images would be huge
    }

    fn learn_clause_lit(&mut self, lit: i32) {
        if self.learned_orbit_k == 0 {
            return;
        }
        if lit == 0 {
            // Clause complete. Generate orbit images and enqueue.
            if self.learned_buf.is_empty() {
                return;
            }
            let clause = std::mem::take(&mut self.learned_buf);
            let gens = &self.gen_set.gens;
            let n_vars = self.gen_set.n_vars;

            let mut seen: HashSet<Vec<i32>> = HashSet::new();
            seen.insert({ let mut c = clause.clone(); c.sort(); c });

            for _ in 0..self.learned_orbit_k {
                // Random group element h via Cayley walk.
                let mut h = Permutation::identity(n_vars);
                for _ in 0..12 {
                    self.orbit_rng = self.orbit_rng
                        .wrapping_mul(6364136223846793005)
                        .wrapping_add(1442695040888963407);
                    let idx = (self.orbit_rng >> 33) as usize % gens.len();
                    let use_inv = (self.orbit_rng >> 16) & 1 == 1;
                    let step = if use_inv {
                        gens[idx].inverse()
                    } else {
                        gens[idx].clone()
                    };
                    h = step.compose(&h);
                }

                let image = h.apply_clause(&clause);
                let mut canon = image.clone();
                canon.sort();
                if seen.insert(canon) && !image.is_empty() {
                    self.external_queue.push(image);
                    self.stats.orbit_images_emitted += 1;
                }
            }
        } else {
            self.learned_buf.push(lit);
        }
    }

    fn has_external_clause(&mut self, is_forgettable: &mut bool) -> bool {
        *is_forgettable = true; // forgettable to avoid DB bloat
        self.external_cursor < self.external_queue.len()
    }

    fn add_external_clause_lit(&mut self) -> i32 {
        if self.external_cursor >= self.external_queue.len() {
            return 0;
        }
        let clause = &self.external_queue[self.external_cursor];
        if self.external_lit_cursor < clause.len() {
            let lit = clause[self.external_lit_cursor];
            self.external_lit_cursor += 1;
            lit
        } else {
            // Clause done; advance to next.
            self.external_cursor += 1;
            self.external_lit_cursor = 0;
            0 // 0-terminate this clause
        }
    }

    fn check_found_model(&mut self, model: &[i32]) -> bool {
        // Verify: for every generator g, the model π satisfies
        // π ≤_lex g(π) under `ordering`. Performed naively — only
        // invoked once per SAT verdict.
        let mut assign = vec![Lbool::Undef; self.gen_set.n_vars as usize + 1];
        for &l in model {
            let v = l.unsigned_abs() as usize;
            if v == 0 || v > self.gen_set.n_vars as usize {
                continue;
            }
            assign[v] = if l > 0 { Lbool::True } else { Lbool::False };
        }
        for gen in &self.gen_set.gens {
            let mut ok = false; // "ok" = found a strictly-smaller position OR ran off end
            for &v in &self.ordering {
                let gv_lit = gen.apply_var(v);
                if gv_lit == v as i32 {
                    continue;
                }
                let a = lit_value(v as i32, &assign);
                let b = lit_value(gv_lit, &assign);
                match (a, b) {
                    // MIN: orig strictly smaller → canonical at this pos.
                    (Lbool::False, Lbool::True) => { ok = true; break; }
                    // MIN: orig strictly greater → non-canonical.
                    (Lbool::True, Lbool::False) => return false,
                    _ => {} // equal or undetermined — continue
                }
            }
            // Running off the end means equality throughout; that's OK.
            let _ = ok;
        }
        true
    }
}

impl Drop for SymmetryPropagator {
    fn drop(&mut self) {
        if std::env::var("CASCADE_SYM_STATS").is_ok() {
            eprintln!(
                "c [sym-stats] assignments={} propagations={} conflicts={} orbit_images={} \
                 prop_enabled={} orbit_k={}",
                self.stats.assignments_processed,
                self.stats.propagations_emitted,
                self.stats.conflicts_emitted,
                self.stats.orbit_images_emitted,
                self.propagation_enabled,
                self.orbit_closure_k,
            );
            let top_violators: Vec<(usize, u64)> = self.stats.violations_by_gen
                .iter().enumerate().map(|(i, &c)| (i, c))
                .filter(|(_, c)| *c > 0).collect();
            let top_propagators: Vec<(usize, u64)> = self.stats.propagations_by_gen
                .iter().enumerate().map(|(i, &c)| (i, c))
                .filter(|(_, c)| *c > 0).collect();
            if !top_violators.is_empty() {
                eprintln!("c [sym-stats] violations by gen: {:?}", top_violators);
            }
            if !top_propagators.is_empty() {
                eprintln!("c [sym-stats] propagations by gen: {:?}", top_propagators);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symmetry::generators::Permutation;

    fn make_single_gen(n_vars: u32, pairs: &[(u32, i32)]) -> GeneratorSet {
        let mut gs = GeneratorSet::empty(n_vars);
        gs.push(Permutation::from_mapping(n_vars, pairs));
        gs
    }

    #[test]
    fn new_propagator_has_empty_trail_and_level_zero() {
        let gs = make_single_gen(3, &[(1, 2), (2, 1)]);
        let p = SymmetryPropagator::new(gs);
        assert_eq!(p.level, 0);
        assert!(p.trail.is_empty());
        assert_eq!(p.comparators.len(), 1);
        assert_eq!(p.observed_vars(), vec![1, 2, 3]);
    }

    #[test]
    fn notify_assignment_updates_assign_mirror() {
        let gs = make_single_gen(3, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1, -3]);
        assert_eq!(p.assign[1], Lbool::True);
        assert_eq!(p.assign[2], Lbool::Undef);
        assert_eq!(p.assign[3], Lbool::False);
        assert_eq!(p.trail, vec![1, 3]);
    }

    #[test]
    fn violation_emits_conflict_from_propagate() {
        // MIN: swap(1,2). v1=T, v2=F → T>F → violation.
        // BC: -1, +2. Propagated lit = last = +2 (currently False).
        let gs = make_single_gen(3, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1, -2]);
        let lit = p.propagate();
        assert_eq!(lit, 2);
        assert_eq!(p.add_reason_clause_lit(2), 2);
        assert_eq!(p.add_reason_clause_lit(2), -1);
        assert_eq!(p.add_reason_clause_lit(2), 0);
    }

    #[test]
    fn no_violation_propagate_returns_zero() {
        // MIN: v1=F, v2=T → F<T → Satisfied.
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[-1, 2]);
        assert_eq!(p.propagate(), 0);
    }

    #[test]
    fn backtrack_clears_pending_and_rewinds_comparators() {
        let gs = make_single_gen(3, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);

        p.notify_new_decision_level();
        // MIN: v1=T, v2=F triggers violation.
        p.notify_assignment(&[1, -2]);
        assert!(p.pending.len() >= 1);

        p.notify_backtrack(0);
        assert_eq!(p.pending.len(), 0);
        assert_eq!(p.level, 0);
        assert_eq!(p.assign[1], Lbool::Undef);
        assert_eq!(p.assign[2], Lbool::Undef);
        assert_eq!(p.comparators[0].status(), CmpStatus::Undecided);
    }

    #[test]
    fn check_found_model_accepts_canonical_model() {
        // MIN: canonical = lex-smallest. For swap(1,2), canonical means
        // val(1) ≤ val(2).
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        assert!(p.check_found_model(&[-1, 2]));  // (F,T) ≤ (T,F)
        assert!(p.check_found_model(&[-1, -2])); // (F,F) = (F,F)
        assert!(p.check_found_model(&[1, 2]));   // (T,T) = (T,T)
    }

    #[test]
    fn check_found_model_rejects_non_canonical() {
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        // MIN: (T,F) > (F,T); (T,F) is non-canonical.
        assert!(!p.check_found_model(&[1, -2]));
    }

    #[test]
    fn multiple_generators_independent_comparators() {
        let mut gs = GeneratorSet::empty(4);
        gs.push(Permutation::from_mapping(4, &[(1, 2), (2, 1)]));
        gs.push(Permutation::from_mapping(4, &[(3, 4), (4, 3)]));
        let mut p = SymmetryPropagator::new(gs);

        // MIN: v1=T, v2=F triggers gen-0 violation.
        p.notify_assignment(&[1, -2]);
        assert!(p.pending.len() >= 1);
        assert!(p.stats.violations_by_gen[0] >= 1);
        assert_eq!(p.stats.violations_by_gen[1], 0);
    }

    #[test]
    fn stats_are_updated() {
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1, -2]);
        let _ = p.propagate();
        assert!(p.stats.assignments_processed >= 2);
        assert_eq!(p.stats.conflicts_emitted, 1);
    }

    // ─── PR-4b: proactive propagation ──

    #[test]
    fn propagation_fires_when_v_true_gv_undef() {
        // MIN: v1=T, v2=Undef → must propagate v2=T.
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1]);
        let lit = p.propagate();
        assert_eq!(lit, 2);
        assert_eq!(p.stats.propagations_emitted, 1);
        assert_eq!(p.stats.conflicts_emitted, 0);
    }

    #[test]
    fn propagation_fires_when_v_undef_gv_false() {
        // MIN: v2=F, v1=Undef → must propagate v1=F.
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[-2]);
        let lit = p.propagate();
        assert_eq!(lit, -1);
        assert_eq!(p.stats.propagations_emitted, 1);
    }

    #[test]
    fn propagation_reason_well_formed() {
        // MIN: v1=T → Propagate(+2). Reason: [+2, -1].
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1]);
        let lit = p.propagate();
        assert_eq!(lit, 2);
        assert_eq!(p.add_reason_clause_lit(2), 2);
        assert_eq!(p.add_reason_clause_lit(2), -1);
        assert_eq!(p.add_reason_clause_lit(2), 0);
    }

    #[test]
    fn propagation_with_equality_prefix() {
        // MIN: 4-cycle (1 2 3 4). v1=T, v2=T → Propagate(+3).
        // Reason: [+3, -1, -2].
        let gs = make_single_gen(4, &[(1, 2), (2, 3), (3, 4), (4, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1, 2]);
        let lit = p.propagate();
        assert_eq!(lit, 3);
        let mut reason = Vec::new();
        loop {
            let l = p.add_reason_clause_lit(3);
            if l == 0 { break; }
            reason.push(l);
        }
        let mut sorted = reason.clone();
        sorted.sort();
        assert_eq!(sorted, vec![-2, -1, 3]);
    }

    #[test]
    fn propagation_prevents_later_violation() {
        // MIN: v1=T → propagate v2=T → equal → Satisfied.
        let gs = make_single_gen(2, &[(1, 2), (2, 1)]);
        let mut p = SymmetryPropagator::new(gs);
        p.notify_assignment(&[1]);
        let lit = p.propagate();
        assert_eq!(lit, 2);
        p.notify_assignment(&[2]);
        assert_eq!(p.propagate(), 0);
        assert_eq!(p.comparators[0].status(), CmpStatus::Satisfied);
        assert_eq!(p.stats.conflicts_emitted, 0);
    }
}
