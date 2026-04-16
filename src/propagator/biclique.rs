//! IPASIR-UP biclique propagator for Ramsey clique-ban constraints.
//!
//! Instead of encoding C(n,s) ban clauses in the CNF, this propagator
//! handles them natively via biclique group at-most-k constraints.
//!
//! When CaDiCaL assigns an edge variable, the propagator:
//!   1. Updates all biclique groups containing that edge
//!   2. If any group reaches threshold+1 true edges, propagates the rest
//!   3. Returns reason clauses on demand (the threshold+1 true edges)
//!
//! This replaces ~2M ban clauses with ~2n groups, each with O(n) edges.

use crate::biclique::{BiclDecomp, BiclGroup};
use crate::cadical::ExternalPropagator;

/// State of an edge variable in the propagator.
#[derive(Clone, Copy, PartialEq, Eq)]
enum EdgeState {
    Unassigned,
    True,  // red
    False, // blue
}

/// A pending propagation: edge variable to propagate + which group caused it.
#[derive(Clone)]
struct PendingProp {
    /// Literal to propagate (positive = set true/red, negative = set false/blue).
    lit: i32,
    /// Index into the group list that triggered this propagation.
    group_idx: usize,
    /// Whether this is a red group (true) or blue group (false).
    is_red: bool,
}

/// Stored reason for a propagation — survives backtracking.
/// Stores the actual antecedent literals at the time of propagation.
#[derive(Clone)]
struct PropReason {
    /// The full reason clause: propagated_lit ∨ ¬ante1 ∨ ¬ante2 ∨ ...
    clause: Vec<i32>,
}

/// Per-group tracking state.
struct GroupState {
    n_true: u32,  // number of edges currently true (red for red groups, blue for blue groups)
    n_false: u32, // number of edges currently false
}

pub struct BicliquePropagator {
    decomp: BiclDecomp,

    /// Assignment state for each edge variable (1-indexed, 0 unused).
    assign: Vec<EdgeState>,

    /// Per-group state for red groups.
    red_state: Vec<GroupState>,
    /// Per-group state for blue groups.
    blue_state: Vec<GroupState>,

    /// edge_to_red_groups[e] = list of (group_idx) for red groups containing edge e.
    edge_to_red_groups: Vec<Vec<usize>>,
    /// edge_to_blue_groups[e] = list of (group_idx) for blue groups containing edge e.
    edge_to_blue_groups: Vec<Vec<usize>>,

    /// Queue of pending propagations.
    pending: Vec<PendingProp>,
    /// Current position in the pending queue.
    pending_head: usize,

    /// Stored reasons: maps propagated literal → group that caused it.
    /// This survives backtracking so CaDiCaL can ask for reasons later.
    reasons: std::collections::HashMap<i32, PropReason>,

    /// Trail: (edge_var, old_state) for each assignment, for backtracking.
    trail: Vec<Vec<(u32, EdgeState)>>,
    /// Current decision level.
    level: usize,

    /// For reason clause generation: stores the reason lits temporarily.
    reason_lits: Vec<i32>,
    reason_pos: usize,
}

impl BicliquePropagator {
    pub fn new(decomp: BiclDecomp) -> Self {
        let n_edges = decomp.n_edges as usize;

        // Build reverse index: edge → groups
        let mut edge_to_red = vec![Vec::new(); n_edges + 1];
        let mut edge_to_blue = vec![Vec::new(); n_edges + 1];

        for (gi, group) in decomp.red_groups.iter().enumerate() {
            for &e in &group.edges {
                edge_to_red[e as usize].push(gi);
            }
        }
        for (gi, group) in decomp.blue_groups.iter().enumerate() {
            for &e in &group.edges {
                edge_to_blue[e as usize].push(gi);
            }
        }

        let n_red = decomp.red_groups.len();
        let n_blue = decomp.blue_groups.len();

        let red_state: Vec<GroupState> = (0..n_red)
            .map(|_| GroupState { n_true: 0, n_false: 0 })
            .collect();
        let blue_state: Vec<GroupState> = (0..n_blue)
            .map(|_| GroupState { n_true: 0, n_false: 0 })
            .collect();

        BicliquePropagator {
            decomp,
            assign: vec![EdgeState::Unassigned; n_edges + 1],
            red_state,
            blue_state,
            edge_to_red_groups: edge_to_red,
            edge_to_blue_groups: edge_to_blue,
            pending: Vec::new(),
            pending_head: 0,
            reasons: std::collections::HashMap::new(),
            trail: vec![Vec::new()], // level 0
            level: 0,
            reason_lits: Vec::new(),
            reason_pos: 0,
        }
    }

    /// Observed variables: all edge variables.
    pub fn observed_vars(&self) -> Vec<i32> {
        (1..=self.decomp.n_edges as i32).collect()
    }

    /// Process an assignment and check for propagations.
    fn process_assignment(&mut self, lit: i32) {
        let var = lit.unsigned_abs() as u32;
        let is_true = lit > 0;
        let n_edges = self.decomp.n_edges as usize;

        if var == 0 || var as usize > n_edges {
            return;
        }

        let old_state = self.assign[var as usize];
        if old_state != EdgeState::Unassigned {
            return; // Already assigned
        }

        let new_state = if is_true { EdgeState::True } else { EdgeState::False };
        self.assign[var as usize] = new_state;

        // Record on trail for backtracking
        if self.level < self.trail.len() {
            self.trail[self.level].push((var, old_state));
        }

        // Update red groups: edge becoming true (red) increases red count
        for &gi in &self.edge_to_red_groups[var as usize] {
            let group = &self.decomp.red_groups[gi];
            let state = &mut self.red_state[gi];
            if is_true {
                state.n_true += 1;
                // Check if we exceeded threshold
                if state.n_true == group.threshold + 1 {
                    // Propagate all remaining unassigned edges to false (blue)
                    for &e in &group.edges {
                        if self.assign[e as usize] == EdgeState::Unassigned {
                            self.pending.push(PendingProp {
                                lit: -(e as i32), // propagate to false/blue
                                group_idx: gi,
                                is_red: true,
                            });
                        }
                    }
                }
            } else {
                state.n_false += 1;
            }
        }

        // Update blue groups: edge becoming false (blue) increases blue count
        for &gi in &self.edge_to_blue_groups[var as usize] {
            let group = &self.decomp.blue_groups[gi];
            let state = &mut self.blue_state[gi];
            if !is_true {
                // Edge is blue (false in original encoding)
                state.n_true += 1; // "true" in the blue sense
                if state.n_true == group.threshold + 1 {
                    // Propagate remaining unassigned edges to true (red)
                    for &e in &group.edges {
                        if self.assign[e as usize] == EdgeState::Unassigned {
                            self.pending.push(PendingProp {
                                lit: e as i32, // propagate to true/red
                                group_idx: gi,
                                is_red: false,
                            });
                        }
                    }
                }
            } else {
                state.n_false += 1;
            }
        }
    }

    /// Load the pre-built reason clause for a propagated literal.
    fn load_reason(&mut self, propagated_lit: i32) {
        self.reason_lits.clear();
        if let Some(reason) = self.reasons.get(&propagated_lit) {
            self.reason_lits.extend_from_slice(&reason.clause);
        } else {
            // Fallback: just the propagated literal
            self.reason_lits.push(propagated_lit);
        }
        self.reason_pos = 0;
    }
}

impl ExternalPropagator for BicliquePropagator {
    fn notify_assignment(&mut self, lits: &[i32]) {
        for &lit in lits {
            self.process_assignment(lit);
        }
    }

    fn notify_new_decision_level(&mut self) {
        self.level += 1;
        if self.level >= self.trail.len() {
            self.trail.push(Vec::new());
        } else {
            self.trail[self.level].clear();
        }
    }

    fn notify_backtrack(&mut self, new_level: usize) {
        // Undo assignments from level new_level+1 to current level
        while self.level > new_level {
            if self.level < self.trail.len() {
                for &(var, _old_state) in self.trail[self.level].iter().rev() {
                    let was_true = self.assign[var as usize] == EdgeState::True;
                    let was_false = self.assign[var as usize] == EdgeState::False;
                    self.assign[var as usize] = EdgeState::Unassigned;

                    // Undo group state
                    for &gi in &self.edge_to_red_groups[var as usize] {
                        if was_true {
                            self.red_state[gi].n_true -= 1;
                        } else if was_false {
                            self.red_state[gi].n_false -= 1;
                        }
                    }
                    for &gi in &self.edge_to_blue_groups[var as usize] {
                        if was_false {
                            self.blue_state[gi].n_true -= 1;
                        } else if was_true {
                            self.blue_state[gi].n_false -= 1;
                        }
                    }
                }
                self.trail[self.level].clear();
            }
            self.level -= 1;
        }

        // Clear pending propagations — they're no longer valid
        self.pending.clear();
        self.pending_head = 0;
    }

    fn propagate(&mut self) -> i32 {
        // Return the next pending propagation
        while self.pending_head < self.pending.len() {
            let prop = self.pending[self.pending_head].clone();
            let var = prop.lit.unsigned_abs() as usize;
            self.pending_head += 1;

            // Only propagate if still unassigned
            if var > 0 && var <= self.decomp.n_edges as usize
                && self.assign[var] == EdgeState::Unassigned
            {
                // Build reason clause NOW (captures correct antecedents)
                let group = if prop.is_red {
                    &self.decomp.red_groups[prop.group_idx]
                } else {
                    &self.decomp.blue_groups[prop.group_idx]
                };

                let mut clause = Vec::new();
                clause.push(prop.lit); // propagated literal first

                let threshold = group.threshold;
                let mut count = 0;
                let prop_var = prop.lit.unsigned_abs() as u32;

                for &e in &group.edges {
                    if count > threshold { break; }
                    if e == prop_var { continue; }
                    if prop.is_red {
                        if self.assign[e as usize] == EdgeState::True {
                            clause.push(-(e as i32));
                            count += 1;
                        }
                    } else {
                        if self.assign[e as usize] == EdgeState::False {
                            clause.push(e as i32);
                            count += 1;
                        }
                    }
                }

                self.reasons.insert(prop.lit, PropReason { clause });
                return prop.lit;
            }
        }
        0 // nothing to propagate
    }

    fn add_reason_clause_lit(&mut self, propagated_lit: i32) -> i32 {
        // First call for this propagated_lit: load the pre-built reason
        if self.reason_lits.is_empty() {
            self.load_reason(propagated_lit);
        }

        if self.reason_pos < self.reason_lits.len() {
            let lit = self.reason_lits[self.reason_pos];
            self.reason_pos += 1;
            lit
        } else {
            // Done — return 0 to terminate the clause, reset for next call
            self.reason_pos = 0;
            self.reason_lits.clear();
            0
        }
    }

    fn check_found_model(&mut self, model: &[i32]) -> bool {
        // Verify no monochromatic clique exists in the model
        let n = self.decomp.n as usize;
        let s = self.decomp.s;
        let t = self.decomp.t;

        // Build edge color lookup from model
        let mut is_red = vec![false; self.decomp.n_edges as usize + 1];
        for &lit in model {
            let var = lit.unsigned_abs() as usize;
            if var > 0 && var <= self.decomp.n_edges as usize {
                is_red[var] = lit > 0;
            }
        }

        // Check all K_s subsets for red monochromatic clique
        // (brute force for correctness — only called once on SAT)
        if s <= n as u32 {
            if has_monochromatic_clique(n as u32, s, &is_red, true, self.decomp.n) {
                return false;
            }
        }
        // Check all K_t subsets for blue monochromatic clique
        if t <= n as u32 {
            if has_monochromatic_clique(n as u32, t, &is_red, false, self.decomp.n) {
                return false;
            }
        }

        true
    }
}

/// Check if there exists a monochromatic clique of size k in the given coloring.
fn has_monochromatic_clique(
    n: u32,
    k: u32,
    is_red: &[bool],
    want_red: bool,
    total_n: u32,
) -> bool {
    if k <= 1 {
        return true;
    }
    // Simple recursive enumeration
    let mut subset = vec![0u32; k as usize];
    check_clique_recursive(&mut subset, 0, 1, n, k, is_red, want_red, total_n)
}

fn check_clique_recursive(
    subset: &mut Vec<u32>,
    depth: usize,
    start: u32,
    n: u32,
    k: u32,
    is_red: &[bool],
    want_red: bool,
    total_n: u32,
) -> bool {
    if depth == k as usize {
        return true; // Found a complete monochromatic clique
    }
    for v in start..=n {
        // Check that v is connected to all previous vertices in the right color
        let mut ok = true;
        for i in 0..depth {
            let u = subset[i];
            let (a, b) = if u < v { (u, v) } else { (v, u) };
            let e = crate::cardinality::ev(a, b, total_n).raw() as usize;
            if is_red[e] != want_red {
                ok = false;
                break;
            }
        }
        if ok {
            subset[depth] = v;
            if check_clique_recursive(subset, depth + 1, v + 1, n, k, is_red, want_red, total_n) {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::biclique;

    #[test]
    fn propagator_basic() {
        // R(3,3)/K_6: threshold 1 per vertex
        let decomp = biclique::decompose(6, 3, 3);
        let mut prop = BicliquePropagator::new(decomp);
        assert_eq!(prop.observed_vars().len(), 15); // C(6,2) = 15 edges

        // Assign edge 1 (vertices 1-2) to red
        prop.notify_assignment(&[1]);

        // With threshold=1 at vertex 1, assigning edge 1 (v1-v2) to red
        // means 1/1 threshold used. One more red edge at v1 should trigger.
        // Assign edge 2 (vertices 1-3) to red
        prop.notify_assignment(&[2]);

        // Now vertex 1 has 2 red edges, threshold is 1 → propagation!
        let p = prop.propagate();
        assert!(p < 0, "should propagate remaining v1 edges to blue, got {}", p);
    }
}
