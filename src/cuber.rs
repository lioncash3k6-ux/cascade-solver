//! BCP-guided lookahead cuber for cube-and-conquer.
//!
//! Scores each unassigned variable by tentatively assigning TRUE then FALSE,
//! running BCP, and counting propagations. Variables with the highest total
//! propagation count are the best split points — they most constrain the
//! formula.
//!
//! The cuber produces a list of cubes (partial assignments) that partition
//! the search space. Each cube is solved independently by CaDiCaL.

use crate::dimacs::Cnf;
use crate::types::Lit;

/// A cube: a partial assignment (conjunction of literals).
pub type Cube = Vec<Lit>;

/// Result of the cubing phase.
#[derive(Debug)]
pub struct CubeResult {
    /// The generated cubes.
    pub cubes: Vec<Cube>,
    /// Variables chosen as split points, in order.
    pub split_vars: Vec<u32>,
    /// Propagation scores for the split variables.
    pub scores: Vec<(u32, u32, u32)>, // (var, score_pos, score_neg)
}

/// Literal → watch-list index: positive `v` → `2*v`, negative `-v` → `2*v + 1`.
#[inline]
fn wlit_idx(lit: i32) -> usize {
    let v = lit.unsigned_abs() as usize;
    2 * v + if lit < 0 { 1 } else { 0 }
}

/// Two-watched-literal BCP for lookahead scoring.
///
/// Watches naturally support checkpoint/restore: watches only migrate away
/// from falsified literals, so after unassigning (restore), the invariant
/// "both watches are non-false" still holds. Over many tentative runs the
/// watch distribution degrades slightly but correctness is preserved.
struct WatchedBcp {
    n: usize,
    clause_db: Vec<Vec<i32>>,       // mutable for watch-slot swaps
    watches: Vec<Vec<usize>>,       // watches[wlit_idx(¬w)] = clauses watching w
    assign: Vec<i8>,                // 0=unset, 1=true, -1=false
}

impl WatchedBcp {
    fn new(cnf: &Cnf) -> Self {
        let n = cnf.nvars as usize;
        let n_lits = 2 * (n + 1);

        let clause_db: Vec<Vec<i32>> = cnf
            .clauses
            .iter()
            .map(|c| c.lits().iter().map(|l| l.raw()).collect())
            .collect();

        let mut watches: Vec<Vec<usize>> = vec![Vec::new(); n_lits];
        let assign = vec![0i8; n + 1];

        // Initialize watches for clauses with >= 2 literals.
        // Watched positions are slots 0 and 1 in each clause.
        for (ci, clause) in clause_db.iter().enumerate() {
            if clause.len() >= 2 {
                watches[wlit_idx(-clause[0])].push(ci);
                watches[wlit_idx(-clause[1])].push(ci);
            }
        }

        WatchedBcp { n, clause_db, watches, assign }
    }

    /// Run 2WL BCP from `prop_head` to end of trail.
    /// Returns (propagation_count, conflict).
    fn propagate(&mut self, trail: &mut Vec<i32>, mut prop_head: usize) -> (usize, bool) {
        let start_len = trail.len();

        while prop_head < trail.len() {
            let lit = trail[prop_head];
            prop_head += 1;
            // Visit clauses watching ¬lit (they just had a watch falsified).
            let lit_i = wlit_idx(lit);

            let old_watches = std::mem::take(&mut self.watches[lit_i]);

            'clause_loop: for &ci in old_watches.iter() {
                let clause = &mut self.clause_db[ci];
                let neg = -lit; // the falsified literal

                // Put the falsified watch in slot 1 so slot 0 is "the other watch".
                if clause[0] == neg {
                    clause.swap(0, 1);
                }

                let other = clause[0];
                let other_v = other.unsigned_abs() as usize;
                let other_val = if other > 0 { 1i8 } else { -1i8 };

                // Fast path: other watch is already satisfied.
                if other_v > 0 && other_v <= self.n && self.assign[other_v] == other_val {
                    self.watches[lit_i].push(ci);
                    continue;
                }

                // Scan for a non-falsified replacement watch.
                for j in 2..clause.len() {
                    let l = clause[j];
                    let v = l.unsigned_abs() as usize;
                    if v == 0 || v > self.n {
                        // Out-of-range — treat as valid replacement.
                        clause.swap(1, j);
                        self.watches[wlit_idx(-clause[1])].push(ci);
                        continue 'clause_loop;
                    }
                    let l_val = if l > 0 { 1i8 } else { -1i8 };
                    if self.assign[v] != -l_val {
                        // Not falsified — promote to watch slot.
                        clause.swap(1, j);
                        self.watches[wlit_idx(-clause[1])].push(ci);
                        continue 'clause_loop;
                    }
                }

                // No replacement: clause is unit or conflict. Keep on this list.
                self.watches[lit_i].push(ci);

                if other_v == 0 || other_v > self.n {
                    continue;
                }
                match self.assign[other_v] {
                    0 => {
                        self.assign[other_v] = other_val;
                        trail.push(other);
                    }
                    cur if cur == other_val => {}
                    _ => {
                        return (trail.len() - start_len, true);
                    }
                }
            }
        }

        (trail.len() - start_len, false)
    }

    /// Tentatively assign a literal and propagate. Returns (props, conflict).
    /// Does NOT undo — caller must use checkpoint/restore.
    fn tentative_assign(&mut self, lit: i32, trail: &mut Vec<i32>) -> (usize, bool) {
        let v = lit.unsigned_abs() as usize;
        if v == 0 || v > self.n || self.assign[v] != 0 {
            return (0, false);
        }
        let val = if lit > 0 { 1i8 } else { -1i8 };
        self.assign[v] = val;
        let prop_head = trail.len();
        trail.push(lit);
        self.propagate(trail, prop_head)
    }

    /// Save checkpoint: returns current trail length.
    fn checkpoint(&self, trail: &[i32]) -> usize {
        trail.len()
    }

    /// Restore to checkpoint: undo all assignments after the checkpoint.
    /// Watch lists remain valid — watches only migrated to non-false positions.
    fn restore(&mut self, trail: &mut Vec<i32>, checkpoint: usize) {
        while trail.len() > checkpoint {
            let lit = trail.pop().unwrap();
            let v = lit.unsigned_abs() as usize;
            self.assign[v] = 0;
        }
    }

    /// Check if variable is assigned.
    fn is_assigned(&self, v: u32) -> bool {
        let vi = v as usize;
        vi > 0 && vi <= self.n && self.assign[vi] != 0
    }
}

/// Score all unassigned variables by lookahead BCP impact.
/// Returns sorted (var, score) pairs, highest score first.
fn score_variables(bcp: &mut WatchedBcp, trail: &mut Vec<i32>, max_vars: u32) -> Vec<(u32, u32)> {
    let mut scores: Vec<(u32, u32)> = Vec::new();

    // Only score original edge variables (1..=max_vars), not aux vars
    let limit = max_vars.min(bcp.n as u32);

    for v in 1..=limit {
        if bcp.is_assigned(v) {
            continue;
        }

        let cp = bcp.checkpoint(trail);

        // Try positive
        let (pos_props, pos_conflict) = bcp.tentative_assign(v as i32, trail);
        bcp.restore(trail, cp);

        // Try negative
        let (neg_props, neg_conflict) = bcp.tentative_assign(-(v as i32), trail);
        bcp.restore(trail, cp);

        // Score: product of propagations (balances the split)
        // Conflicts count as very high score (the branch is immediately closed)
        let pos_score = if pos_conflict { 10000 } else { pos_props as u32 };
        let neg_score = if neg_conflict { 10000 } else { neg_props as u32 };
        let score = pos_score.saturating_mul(neg_score).max(pos_score + neg_score);

        scores.push((v, score));
    }

    scores.sort_by(|a, b| b.1.cmp(&a.1));
    scores
}

/// Generate cubes by splitting on the top-k highest-scoring variables.
///
/// `cnf`: the augmented formula (after satsuma + card + chain)
/// `depth`: number of split variables (2^depth cubes)
/// `max_edge_var`: only score variables up to this index (skip aux vars)
///
/// Returns the cubes and metadata about which variables were chosen.
pub fn generate_cubes(cnf: &Cnf, depth: u32, max_edge_var: u32) -> CubeResult {
    let mut bcp = WatchedBcp::new(cnf);
    let mut trail: Vec<i32> = Vec::new();

    // Initial BCP from unit clauses (not watched by 2WL, handled separately)
    for clause in cnf.clauses.iter() {
        if clause.len() == 1 {
            let lit = clause.lits()[0].raw();
            let v = lit.unsigned_abs() as usize;
            if v > 0 && v <= bcp.n && bcp.assign[v] == 0 {
                let val = if lit > 0 { 1i8 } else { -1i8 };
                bcp.assign[v] = val;
                trail.push(lit);
            }
        }
    }
    let _ = bcp.propagate(&mut trail, 0);

    // Score and select split variables
    let scores_all = score_variables(&mut bcp, &mut trail, max_edge_var);
    let depth = depth.min(scores_all.len() as u32);

    let mut split_vars = Vec::new();
    let mut score_info = Vec::new();
    for i in 0..depth as usize {
        let (var, _score) = scores_all[i];
        split_vars.push(var);

        // Record individual pos/neg scores for diagnostics
        let cp = bcp.checkpoint(&trail);
        let (ps, _) = bcp.tentative_assign(var as i32, &mut trail);
        bcp.restore(&mut trail, cp);
        let (ns, _) = bcp.tentative_assign(-(var as i32), &mut trail);
        bcp.restore(&mut trail, cp);
        score_info.push((var, ps as u32, ns as u32));
    }

    // Generate 2^depth cubes
    let n_cubes = 1u64 << depth;
    let mut cubes = Vec::with_capacity(n_cubes as usize);
    for i in 0..n_cubes {
        let mut cube = Vec::with_capacity(depth as usize);
        for (b, &var) in split_vars.iter().enumerate() {
            let lit = if (i >> b) & 1 == 0 {
                Lit::new(var as i32)
            } else {
                Lit::new(-(var as i32))
            };
            cube.push(lit);
        }
        cubes.push(cube);
    }

    CubeResult {
        cubes,
        split_vars,
        scores: score_info,
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
    fn cuber_trivial_unsat() {
        // x1 ∧ ¬x1 — BCP closes immediately, 0 cubes needed
        let cnf = parse("p cnf 2 3\n1 0\n-1 0\n1 2 0\n");
        let result = generate_cubes(&cnf, 1, 2);
        // Should still generate cubes (cuber doesn't solve, just splits)
        assert_eq!(result.cubes.len(), 2);
    }

    #[test]
    fn cuber_generates_correct_count() {
        let cnf = parse("p cnf 5 3\n1 2 3 0\n-1 -2 0\n4 5 0\n");
        let result = generate_cubes(&cnf, 2, 5);
        assert_eq!(result.cubes.len(), 4); // 2^2
        assert_eq!(result.split_vars.len(), 2);
    }

    #[test]
    fn cuber_scores_constrained_vars_higher() {
        // x1 appears in many clauses, x5 in few
        let cnf = parse(
            "p cnf 5 6\n1 2 0\n-1 3 0\n1 -3 0\n-1 -2 0\n1 4 0\n4 5 0\n",
        );
        let result = generate_cubes(&cnf, 2, 5);
        // x1 should score highest (appears in 5 clauses)
        assert_eq!(result.split_vars[0], 1);
    }
}
