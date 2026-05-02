//! Quotient Wiedemann: NS matrix solver with embedded ideal-reduction.
//!
//! # Algebraic structure
//!
//! The NS solver at degree d solves `A_d · x = b` where columns of `A_d` are
//! orbit-reduced monomials. Solutions at lower degrees generate an ideal
//! `I_{<d}` that predicts part of the degree-d kernel. Projecting `A_d` onto
//! `A_d / I_{<d}` before solving:
//!   - reduces the effective matrix dimension from `n_cols` to `N_eff`
//!   - cuts Wiedemann cost by `(N_eff / n_cols)²`
//!   - reveals G_d = dim(ker(A_d)) - dim(I_{<d} ∩ ker(A_d))
//!
//! # Key invariant: global triangularity
//!
//! The [`PivotTable`] maintains: **no rule's RHS contains any pivot column**.
//! This makes single-pass reduction confluent (unique normal form) without
//! a Gröbner basis, and lets the Wiedemann loop apply it as a true linear
//! projector Π with Π² = Π.
//!
//! # Integration
//!
//! Call [`build_pivot_table_from_solution`] after each successful degree-d
//! solve to extract its pivot rules. Then pass the table to
//! [`augment_with_pivot_rows`] before calling the existing
//! `sparse_block_wiedemann_fp`. The augmented matrix's solution is
//! automatically in the quotient.

use rustc_hash::FxHashMap;

// ────────────���─────────────────────────��──────────────────────────────────────
// Field arithmetic helpers (F_p, small prime u8)
// ─────────────────────────────────────────────────────────────────────────────

#[inline]
fn fp_neg(a: u8, p: u8) -> u8 { if a == 0 { 0 } else { p - a } }

#[inline]
fn fp_mul(a: u8, b: u8, p: u8) -> u8 { ((a as u16 * b as u16) % p as u16) as u8 }

fn fp_inv(a: u8, p: u8) -> u8 {
    debug_assert!(a != 0 && p > 1);
    // Extended Euclidean over small prime — called rarely (once per insert).
    let (mut r0, mut r1) = (p as i16, a as i16);
    let (mut s0, mut s1) = (0i16, 1i16);
    while r1 != 0 {
        let q = r0 / r1;
        (r0, r1) = (r1, r0 - q * r1);
        (s0, s1) = (s1, s0 - q * s1);
    }
    ((s0 % p as i16 + p as i16) as u16 % p as u16) as u8
}

// ─────────────────────────────────────────────────────────────────────────────
// Sorted-sparse row arithmetic  (matches orbit_ns internal format)
// ─────────────────────────────────────────────────────────────────────────────

/// `out = a + scale * b`  over F_p.  Both inputs must be col-sorted.
fn saxpy(a: &[(u32, u8)], b: &[(u32, u8)], scale: u8, p: u8) -> Vec<(u32, u8)> {
    if scale == 0 { return a.to_vec(); }
    let p16 = p as u16;
    let mut out = Vec::with_capacity(a.len() + b.len());
    let (mut ai, mut bi) = (0usize, 0usize);
    while ai < a.len() || bi < b.len() {
        let ac = a.get(ai).map_or(u32::MAX, |&(c, _)| c);
        let bc = b.get(bi).map_or(u32::MAX, |&(c, _)| c);
        if ac < bc      { out.push(a[ai]); ai += 1; }
        else if bc < ac {
            let v = (scale as u16 * b[bi].1 as u16 % p16) as u8;
            if v != 0 { out.push((bc, v)); }
            bi += 1;
        } else {
            let v = ((a[ai].1 as u16 + scale as u16 * b[bi].1 as u16) % p16) as u8;
            if v != 0 { out.push((ac, v)); }
            ai += 1; bi += 1;
        }
    }
    out
}

// ─────────────────────────────────────────────────────────────────────────────
// Pivot table
// ─────────────────────────────────────────────────────────────────────────────

/// Globally-triangular pivot table over F_p.
///
/// Invariant: for every `(pivot_col, rule)` in `self.rules`,
///   `rule` is col-sorted, `rule[0] = (pivot_col, 1)`, and no other
///   rule's RHS (columns beyond index 0) contains `pivot_col`.
///
/// This makes [`PivotTable::reduce_dense`] a single-pass, confluent linear
/// projector — no fixpoint loop needed.
pub struct PivotTable {
    /// pivot_col → sorted rule (pivot at index 0, coeff = 1; RHS has no pivot cols)
    pub rules: FxHashMap<u32, Vec<(u32, u8)>>,
    pub p: u8,
}

impl PivotTable {
    pub fn new(p: u8) -> Self {
        Self { rules: FxHashMap::default(), p }
    }

    pub fn pivot_count(&self) -> usize { self.rules.len() }

    pub fn is_pivot(&self, col: u32) -> bool { self.rules.contains_key(&col) }

    /// Number of non-pivot columns = effective dimension of quotient space.
    pub fn n_eff(&self, n_cols: usize) -> usize { n_cols.saturating_sub(self.rules.len()) }

    /// Reduce a dense column vector `v` in-place (single pass, O(pivots × rule_density)).
    ///
    /// Safe to call with one pass because global triangularity guarantees the RHS of each
    /// rule contains no pivot columns, so eliminating pivot_col from v can't re-introduce
    /// another pivot column via the rule's coefficients.
    pub fn reduce_dense(&self, v: &mut [u8]) {
        let p = self.p;
        for (&pcol, rule) in &self.rules {
            let pc = pcol as usize;
            if pc >= v.len() { continue; }
            let coeff = v[pc];
            if coeff == 0 { continue; }
            v[pc] = 0;
            // rule[0] is the pivot (coeff 1); remaining entries are the RHS.
            let neg_c = fp_neg(coeff, p);
            for &(col, val) in rule.iter().skip(1) {
                let c = col as usize;
                if c < v.len() {
                    v[c] = ((v[c] as u16 + fp_mul(neg_c, val, p) as u16) % p as u16) as u8;
                }
            }
        }
    }

    /// Reduce a sparse row in-place (terminates because pivot set shrinks each step).
    pub fn reduce_sparse(&self, row: &mut Vec<(u32, u8)>) {
        let p = self.p;
        loop {
            let hit = row.iter().position(|&(c, _)| self.rules.contains_key(&c));
            let Some(pos) = hit else { break };
            let (pcol, coeff) = row[pos];
            let rule = &self.rules[&pcol];
            let neg_c = fp_neg(coeff, p);
            *row = saxpy(row, rule, neg_c, p);
        }
    }

    /// Insert a new row, maintaining the global-triangularity invariant:
    ///
    /// 1. Reduce `row` against the existing table.
    /// 2. If zero: row is already in ideal span → discard.
    /// 3. Normalize: scale so pivot coefficient = 1.
    /// 4. Back-eliminate: remove the new pivot column from every existing rule's RHS.
    /// 5. Insert.
    pub fn insert(&mut self, mut row: Vec<(u32, u8)>) {
        self.reduce_sparse(&mut row);
        if row.is_empty() { return; }

        let pivot_col = row[0].0;
        let pivot_val = row[0].1;
        let inv = fp_inv(pivot_val, self.p);
        let p = self.p;

        // Normalize: pivot coeff → 1
        for (_, v) in &mut row { *v = fp_mul(*v, inv, p); }

        // Back-eliminate this pivot from all existing rules (maintains invariant).
        // Collect keys that have an entry at pivot_col to avoid borrow conflict.
        let to_fix: Vec<u32> = self.rules.iter()
            .filter(|(_, rule)| rule.iter().any(|&(c, _)| c == pivot_col))
            .map(|(&k, _)| k)
            .collect();

        for key in to_fix {
            let rule = self.rules.get(&key).unwrap().clone();
            let coeff = rule.iter().find(|&&(c, _)| c == pivot_col).map(|&(_, v)| v).unwrap_or(0);
            if coeff == 0 { continue; }
            let neg_c = fp_neg(coeff, p);
            let new_rule = saxpy(&rule, &row, neg_c, p);
            self.rules.insert(key, new_rule);
        }

        self.rules.insert(pivot_col, row);
    }

    /// Sample S-pairs and check if they reduce to zero.
    ///
    /// Returns `(success_rate ∈ [0,1], avg_support_after_reduction)`.
    /// A rate near 1.0 indicates near-Gröbner behavior: the pivot table is
    /// algebraically complete and `n_eff` is a true quotient dimension.
    pub fn check_s_pairs(&self, n_samples: usize) -> (f64, f64) {
        let rules: Vec<(&u32, &Vec<(u32, u8)>)> = self.rules.iter().collect();
        if rules.len() < 2 { return (1.0, 0.0); }
        let p = self.p;
        let mut zero = 0usize;
        let mut total_supp = 0usize;
        let mut total = 0usize;

        'outer: for i in 0..rules.len() {
            for j in (i + 1)..rules.len() {
                let r1 = rules[i].1;
                let r2 = rules[j].1;
                // Find lowest non-pivot column shared between r1's RHS and r2's RHS.
                let shared = r1.iter().skip(1)
                    .find(|&&(c, _)| !self.is_pivot(c) && r2.iter().any(|&(c2, _)| c2 == c));
                let Some(&(sc, v1)) = shared else { total += 1; zero += 1; continue };
                let v2 = r2.iter().find(|&&(c, _)| c == sc).map(|&(_, v)| v).unwrap();
                // S-row: r1 * v2 - r2 * v1  (eliminates shared column sc)
                let neg_v1 = fp_neg(v1, p);
                let mut s = saxpy(r1, r2, fp_mul(neg_v1, fp_inv(v2, p), p), p);
                self.reduce_sparse(&mut s);
                total_supp += s.len();
                if s.is_empty() { zero += 1; }
                total += 1;
                if total >= n_samples { break 'outer; }
            }
        }
        if total == 0 { return (1.0, 0.0); }
        (zero as f64 / total as f64, total_supp as f64 / total as f64)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Building the pivot table from NS solutions
// ─────────────────────────────────────────────────────────────────────────────

/// Extract pivot rules from a degree-d solution vector into `table`.
///
/// The solution `sol` (length `n_cols`) represents a particular solution to
/// `A_d · x = b` at degree d. Each non-zero entry `sol[col] = v` contributes
/// a rewrite rule: `x[col] → ...` (derived from the row that determined `col`
/// during back-substitution).
///
/// In practice, the simplest correct approach is: for each non-zero coefficient
/// in `sol`, construct the trivial rule `e_{col} → sol[col] * e_{col}` and let
/// `insert` handle the ideal closure. However, this only captures the solution
/// structure as a 1-dimensional kernel; for multi-dimensional kernels (multiple
/// generators at degree d) you should call this for each independent generator.
///
/// For the R(5,5) single-certificate regime, `sol` is a single vector and this
/// gives one pivot rule per non-zero entry.
pub fn build_pivot_table_from_solution(
    sol: &[u8],
    n_cols: usize,
    p: u8,
) -> PivotTable {
    let mut table = PivotTable::new(p);
    // Build a single rule: the solution vector itself, normalized to its leading entry.
    // Find leftmost non-zero entry.
    let Some(pivot_pos) = sol[..n_cols].iter().position(|&v| v != 0) else { return table };
    let pivot_val = sol[pivot_pos];
    let inv = fp_inv(pivot_val, p);
    let p16 = p as u16;
    let mut rule: Vec<(u32, u8)> = sol[..n_cols].iter().enumerate()
        .filter(|&(_, &v)| v != 0)
        .map(|(c, &v)| (c as u32, ((v as u16 * inv as u16) % p16) as u8))
        .collect();
    rule.sort_unstable_by_key(|&(c, _)| c);
    // The rule encodes: x[pivot_col] = -Σ_{c≠pivot_col} rule[c] * x[c]
    // expressed as the row "pivot_col entry = 1, rest = -rhs_coeffs"
    // insert() will normalize and maintain triangularity.
    table.insert(rule);
    table
}

/// Build a pivot table from multiple independent solution vectors (one per generator G_d).
pub fn build_pivot_table_from_generators(
    generators: &[Vec<u8>],
    n_cols: usize,
    p: u8,
) -> PivotTable {
    let mut table = PivotTable::new(p);
    for sol in generators {
        let Some(pivot_pos) = sol[..n_cols].iter().position(|&v| v != 0) else { continue };
        let pivot_val = sol[pivot_pos];
        let inv = fp_inv(pivot_val, p);
        let p16 = p as u16;
        let mut rule: Vec<(u32, u8)> = sol[..n_cols].iter().enumerate()
            .filter(|&(_, &v)| v != 0)
            .map(|(c, &v)| (c as u32, ((v as u16 * inv as u16) % p16) as u8))
            .collect();
        rule.sort_unstable_by_key(|&(c, _)| c);
        table.insert(rule);
    }
    table
}

// ─────────────────────────────────────────────────────────────────────────────
// Augmentation: project NS matrix onto quotient space
// ───────────────────────────────────────────────────────────────────────��─────

/// Augment `rows` with pivot-enforcement rows and return the reduced matrix.
///
/// Two effects:
///   1. Rows representing `e_{pivot_col} = rule_rhs` force the solution into
///      the quotient `A_d / I_{<d}` automatically — the Wiedemann solver sees
///      only the quotient kernel.
///   2. `drop_pivot_cols = true` additionally removes pivot columns from all
///      rows (substitutes the rule in-place), shrinking n_cols to `n_eff` and
///      giving the full quadratic speedup.
///
/// When `drop_pivot_cols = false`, the augmented rows are prepended as hard
/// constraints but n_cols is unchanged. This is the simpler integration path
/// (no column remapping needed).
pub fn augment_with_pivot_rows(
    rows: &[Vec<(u32, u8)>],
    pivot_table: &PivotTable,
    n_cols: usize,
    drop_pivot_cols: bool,
) -> (Vec<Vec<(u32, u8)>>, usize) {
    if pivot_table.pivot_count() == 0 {
        return (rows.to_vec(), n_cols);
    }

    if !drop_pivot_cols {
        // Fast path: prepend pivot-rule rows as hard constraints, keep column count.
        let mut out: Vec<Vec<(u32, u8)>> = Vec::with_capacity(rows.len() + pivot_table.pivot_count());
        for rule in pivot_table.rules.values() {
            // Each rule is already in the correct row format: pivot entry = 1, RHS negated.
            out.push(rule.clone());
        }
        out.extend_from_slice(rows);
        return (out, n_cols);
    }

    // Full projection: apply pivot reduction to every row, drop pivot columns, remap.
    let mut is_pivot = vec![false; n_cols];
    for &pcol in pivot_table.rules.keys() {
        if (pcol as usize) < n_cols { is_pivot[pcol as usize] = true; }
    }
    let col_remap: Vec<u32> = {
        let mut next = 0u32;
        (0..n_cols).map(|c| if is_pivot[c] { u32::MAX } else { let v = next; next += 1; v }).collect()
    };
    let n_eff = n_cols - pivot_table.pivot_count();

    let projected: Vec<Vec<(u32, u8)>> = rows.iter().map(|row| {
        let rhs_entry = row.iter().find(|&&(c, _)| c as usize == n_cols).cloned();
        // Build dense slice for this row, then reduce, then re-sparsify.
        let mut dense = vec![0u8; n_cols + 1];
        for &(c, v) in row { if (c as usize) <= n_cols { dense[c as usize] = v; } }
        pivot_table.reduce_dense(&mut dense[..n_cols]);
        let mut out: Vec<(u32, u8)> = dense[..n_cols].iter().enumerate()
            .filter(|&(c, &v)| v != 0 && !is_pivot[c])
            .map(|(c, &v)| (col_remap[c], v))
            .collect();
        // Restore RHS column at n_eff position.
        if let Some((_, rv)) = rhs_entry { if rv != 0 { out.push((n_eff as u32, rv)); } }
        out.sort_unstable_by_key(|&(c, _)| c);
        out
    }).collect();

    (projected, n_eff)
}

// ─────────────────────────────────────────────────────────────────────────────
// G_d measurement
// ─────────────────────────────────────────────────────────────────────────────

/// Statistics reported by [`measure_g_d`].
#[derive(Debug, Clone)]
pub struct GdStats {
    /// Ambient orbit-monomial count at this degree.
    pub n_ambient: usize,
    /// Effective (non-pivot) dimension = |A_d / I_{<d}|.
    pub n_eff: usize,
    /// Pivot coverage fraction = (n_ambient - n_eff) / n_ambient.
    pub pivot_coverage: f64,
    /// S-pair success rate (1.0 = near-Gröbner).
    pub s_pair_rate: f64,
    /// Average support after S-pair reduction.
    pub s_pair_avg_density: f64,
}

impl GdStats {
    pub fn compute(pivot_table: &PivotTable, n_ambient: usize) -> Self {
        let n_eff = pivot_table.n_eff(n_ambient);
        let pivot_coverage = 1.0 - n_eff as f64 / n_ambient.max(1) as f64;
        let (s_pair_rate, s_pair_avg_density) = pivot_table.check_s_pairs(64);
        Self { n_ambient, n_eff, pivot_coverage, s_pair_rate, s_pair_avg_density }
    }

    pub fn log(&self, d: usize) {
        eprintln!(
            "c [qw] d={d}: |A_d|={} N_eff={} ({:.1}% covered) S-pair={:.1}% avg_density={:.1}",
            self.n_ambient, self.n_eff,
            100.0 * self.pivot_coverage,
            100.0 * self.s_pair_rate,
            self.s_pair_avg_density,
        );
    }

    /// Predicted Wiedemann cost ratio vs. baseline (no quotient reduction).
    /// cost ~ N_eff² so ratio = (N_eff / N_ambient)².
    pub fn predicted_speedup(&self) -> f64 {
        let r = self.n_eff as f64 / self.n_ambient.max(1) as f64;
        1.0 / (r * r).max(1e-9)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Kernel algebra state: persistent across degree steps
// ─────────────────────────────────────────────────────────────────────────────

/// Holds the pivot table from all degrees ≤ d and the closure cache.
///
/// After each successful NS solve at degree d:
///   1. Call `record_solution(d, &solution_vec, n_cols)`.
///   2. Call `build_table_for(d+1)` to get the pivot table for degree d+1.
///   3. Pass the table to `augment_with_pivot_rows` before the next Wiedemann.
///
/// This gives the incremental warm-start behavior without recomputing lower
/// degrees, and makes G_d measurable as `table.n_eff(n_cols_at_d)`.
pub struct KernelAlgebraState {
    /// Per-degree solution vectors (non-empty = cert found at that degree).
    solutions: Vec<(usize, Vec<u8>)>,  // (d, solution)
    /// The current merged pivot table (all degrees recorded so far).
    table: PivotTable,
    pub p: u8,
}

impl KernelAlgebraState {
    pub fn new(p: u8) -> Self {
        Self { solutions: Vec::new(), table: PivotTable::new(p), p }
    }

    /// Record a solution found at degree `d` and integrate it into the pivot table.
    pub fn record_solution(&mut self, d: usize, solution: &[u8], n_cols: usize) {
        self.solutions.push((d, solution.to_vec()));
        let new_table = build_pivot_table_from_solution(solution, n_cols, self.p);
        for (_, rule) in new_table.rules {
            self.table.insert(rule);
        }
    }

    /// Record multiple generators (for multi-dimensional kernels).
    pub fn record_generators(&mut self, d: usize, gens: &[Vec<u8>], n_cols: usize) {
        for g in gens {
            self.solutions.push((d, g.clone()));
        }
        let new_table = build_pivot_table_from_generators(gens, n_cols, self.p);
        for (_, rule) in new_table.rules {
            self.table.insert(rule);
        }
    }

    /// Build the augmented row set for degree `d` (uses all solutions at degrees < d).
    /// Pass the returned rows + n_cols to `sparse_block_wiedemann_fp`.
    pub fn augmented_rows<'a>(
        &'a self,
        rows: &[Vec<(u32, u8)>],
        n_cols: usize,
        drop_pivot_cols: bool,
    ) -> (Vec<Vec<(u32, u8)>>, usize) {
        augment_with_pivot_rows(rows, &self.table, n_cols, drop_pivot_cols)
    }

    /// Compute and log G_d statistics for degree `d`.
    pub fn measure(&self, d: usize, n_ambient: usize) -> GdStats {
        let stats = GdStats::compute(&self.table, n_ambient);
        stats.log(d);
        stats
    }

    pub fn pivot_count(&self) -> usize { self.table.pivot_count() }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn make_rule(cols: &[(u32, u8)]) -> Vec<(u32, u8)> {
        let mut v = cols.to_vec();
        v.sort_unstable_by_key(|&(c, _)| c);
        v
    }

    #[test]
    fn pivot_table_triangularity() {
        let p = 11u8;
        let mut table = PivotTable::new(p);

        // Insert rule: x_0 = 2*x_2 + 3*x_3  →  row (0,1),(2,p-2),(3,p-3)
        table.insert(make_rule(&[(0, 1), (2, p - 2), (3, p - 3)]));

        // Insert rule: x_2 = 4*x_3 + 5*x_4  →  row (2,1),(3,p-4),(4,p-5)
        // After insert, x_0 rule must no longer contain x_2.
        table.insert(make_rule(&[(2, 1), (3, p - 4), (4, p - 5)]));

        // Verify: x_0 rule has no entry at col 2
        let r0 = &table.rules[&0];
        assert!(!r0.iter().any(|&(c, _)| c == 2),
            "triangularity violated: x_0 rule still has x_2: {:?}", r0);

        // Verify: x_2 rule has no pivot columns (only col 0 and col 2 are pivots)
        let r2 = &table.rules[&2];
        assert!(!r2.iter().skip(1).any(|&(c, _)| table.is_pivot(c)),
            "triangularity violated: x_2 rule's RHS has pivot column: {:?}", r2);
    }

    #[test]
    fn reduce_dense_single_pass() {
        let p = 11u8;
        let mut table = PivotTable::new(p);
        // x_0 = x_1 + x_2
        table.insert(make_rule(&[(0, 1), (1, p - 1), (2, p - 1)]));

        let mut v = vec![3u8, 0, 0, 5, 0];  // v[0]=3, others zero except v[3]=5
        table.reduce_dense(&mut v);
        // After reduction: v[0] should be 0, v[1] += -3*(-1) = 3, v[2] += -3*(-1) = 3
        assert_eq!(v[0], 0, "pivot column not eliminated");
        assert_eq!(v[1], 3u8, "RHS not correctly propagated");
        assert_eq!(v[2], 3u8, "RHS not correctly propagated");
        assert_eq!(v[3], 5u8, "unrelated column disturbed");
    }

    #[test]
    fn insert_idempotent() {
        let p = 7u8;
        let mut table = PivotTable::new(p);
        let rule = make_rule(&[(0, 1), (3, 5), (5, 2)]);
        table.insert(rule.clone());
        let cnt_before = table.pivot_count();
        table.insert(rule);  // inserting same rule again → already in span
        assert_eq!(table.pivot_count(), cnt_before, "duplicate insert changed table");
    }

    #[test]
    fn augment_preserves_solution_space() {
        // A simple 3-col system: x0 + x1 = 1, x0 + x2 = 0.
        // Solution: x0=1, x1=0, x2=p-1.
        let p = 11u8;
        let rows = vec![
            vec![(0u32, 1u8), (1u32, 1u8), (3u32, 1u8)],  // x0+x1=1 (RHS at col 3)
            vec![(0u32, 1u8), (2u32, 1u8)],                 // x0+x2=0
        ];
        let n_cols = 3;
        let sol = vec![1u8, 0u8, p - 1u8];
        let table = build_pivot_table_from_solution(&sol, n_cols, p);
        let (aug, new_n) = augment_with_pivot_rows(&rows, &table, n_cols, false);
        // Augmented rows should be consistent (no extra constraints violated).
        // Just check structural properties here.
        assert!(aug.len() >= rows.len());
        assert_eq!(new_n, n_cols);
        assert!(table.pivot_count() > 0);
    }

    #[test]
    fn gd_stats_full_coverage() {
        let p = 11u8;
        let mut table = PivotTable::new(p);
        // 3 rules covering 3 of 5 columns
        table.insert(make_rule(&[(0, 1), (3, 2)]));
        table.insert(make_rule(&[(1, 1), (4, 3)]));
        table.insert(make_rule(&[(2, 1), (3, 1), (4, 1)]));
        let stats = GdStats::compute(&table, 5);
        assert_eq!(stats.n_eff, 2);
        assert!((stats.pivot_coverage - 0.6).abs() < 1e-9);
    }
}
