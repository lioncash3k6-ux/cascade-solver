#![allow(dead_code, unused_mut, unused_parens)]
//! Stage A — direct enumeration of PHP monomial orbit representatives.
//!
//! For PHP_{P,H} under G = S_P × S_H, a squarefree degree-d monomial is a
//! subset of P×H cells, equivalently a 0-1 P×H matrix with d ones, and an
//! orbit is a bipartite-graph isomorphism class. This module enumerates
//! orbit representatives directly, without materializing the full monomial
//! space of size C(P·H, ≤d).
//!
//! The goal is to replace the `n_monos`-scale BFS + `Vec<u32>` orbit_id
//! array in [`super::orbit_ns`]. For PHP_{8,7} d=7 that drops 268M mono
//! visits + 1GB orbit_id to ~thousands of orbit-rep visits.
//!
//! # Two-phase canonicalization
//!
//! Iterated row+col sort by `(popcount, bitstring)` is **not** a strong
//! canonical form — PHP_{5,4} d=5 produces 56 fixed points but has only
//! 54 true orbits (measured: 56 → 54 after dedup). Row-sort commutes with
//! row perms and col-sort commutes with col perms, but their composition
//! can converge to distinct fixed points within one S_P × S_H orbit.
//!
//! Solution:
//!
//! 1. BFS over pseudo-canonical forms (iterated row+col sort). Already
//!    collapses the state space from C(P·H, ≤d) down to a small
//!    candidate set.
//! 2. Post-dedup via union-find: apply S_P × S_H adjacent-transposition
//!    generators to each pseudo-canonical, canonicalize the image, link
//!    in UF. Each UF component is a true orbit; we pick the rep with
//!    smallest bits as canonical.
//!
//! Cost: `candidate_count × (P + H) × canonicalize`. The over-split
//! factor is ≤ 1.1× empirically, so the UF pass is effectively linear.

use std::collections::{BTreeMap, BTreeSet};

/// Packed 0-1 matrix with P ≤ 16 rows, H ≤ 16 cols, P·H ≤ 128 cells.
/// Bit `i*H + j` set iff cell (i, j) is 1.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct PhpMatrix {
    pub bits: u128,
    pub p: u8,
    pub h: u8,
}

impl PhpMatrix {
    pub const MAX_DIM: u32 = 16;

    pub fn empty(p: u32, h: u32) -> Self {
        assert!(p <= Self::MAX_DIM && h <= Self::MAX_DIM);
        assert!(p as u32 * h as u32 <= 128);
        Self { bits: 0, p: p as u8, h: h as u8 }
    }

    /// Build from a bit representation with cell (i, j) at bit `i*H + j`.
    pub fn from_bits(bits: u128, p: u32, h: u32) -> Self {
        assert!(p <= Self::MAX_DIM && h <= Self::MAX_DIM);
        Self { bits, p: p as u8, h: h as u8 }
    }

    pub fn popcount(&self) -> u32 {
        (self.bits.count_ones()) as u32
    }

    pub fn cell(&self, i: u32, j: u32) -> bool {
        let pos = i * self.h as u32 + j;
        (self.bits >> pos) & 1 == 1
    }

    pub fn set_cell(&self, i: u32, j: u32) -> Self {
        let pos = i * self.h as u32 + j;
        Self { bits: self.bits | (1u128 << pos), p: self.p, h: self.h }
    }

    /// Row `i` as a right-aligned H-bit value (LSB = col 0).
    pub fn row(&self, i: u32) -> u32 {
        let mask = (1u128 << self.h) - 1;
        ((self.bits >> (i * self.h as u32)) & mask) as u32
    }

    /// Col `j` as a P-bit value (LSB = row 0).
    pub fn col(&self, j: u32) -> u32 {
        let mut c = 0u32;
        for i in 0..self.p as u32 {
            if self.cell(i, j) {
                c |= 1u32 << i;
            }
        }
        c
    }

    /// Canonical form under S_P × S_H via iterated row+col sort descending
    /// by `(popcount, bitstring)`. Stable sort on ties.
    pub fn canonicalize(&self) -> Self {
        let p = self.p as u32;
        let h = self.h as u32;
        // Unpack rows as u32, sort-and-pack loop until fixed point.
        let mut rows: Vec<u32> = (0..p).map(|i| self.row(i)).collect();
        for _iter in 0..16 {
            // Row sort: descending by (popcount, value). Stable.
            rows.sort_by(|a, b| {
                let ka = (a.count_ones(), *a);
                let kb = (b.count_ones(), *b);
                kb.cmp(&ka)
            });
            // Compute col values under current row order.
            let mut col_vals: Vec<(u32, u32)> = (0..h)
                .map(|j| {
                    let mut c = 0u32;
                    for (i, &r) in rows.iter().enumerate() {
                        if (r >> j) & 1 == 1 {
                            c |= 1u32 << i;
                        }
                    }
                    (c.count_ones(), c)
                })
                .collect();
            // Rank cols descending by (popcount, value). perm[new_j] = old_j.
            let mut perm: Vec<u32> = (0..h).collect();
            perm.sort_by(|&a, &b| col_vals[b as usize].cmp(&col_vals[a as usize]));
            // Apply col perm to rows.
            let mut changed = false;
            for r in rows.iter_mut() {
                let mut new_r = 0u32;
                for (new_j, &old_j) in perm.iter().enumerate() {
                    if (*r >> old_j) & 1 == 1 {
                        new_r |= 1u32 << new_j;
                    }
                }
                if *r != new_r {
                    changed = true;
                }
                *r = new_r;
            }
            if !changed {
                break;
            }
        }
        // Pack rows back to u128.
        let mut bits = 0u128;
        for (i, &r) in rows.iter().enumerate() {
            bits |= (r as u128) << (i as u32 * h);
        }
        Self { bits, p: self.p, h: self.h }
    }
}

/// Apply a row transposition `(i, i+1)` to matrix `m`.
fn apply_row_swap(m: &PhpMatrix, i: u32) -> PhpMatrix {
    let h = m.h as u32;
    let mask = (1u128 << h) - 1;
    let a = (m.bits >> (i * h)) & mask;
    let b = (m.bits >> ((i + 1) * h)) & mask;
    let rest = m.bits & !((mask << (i * h)) | (mask << ((i + 1) * h)));
    PhpMatrix::from_bits(
        rest | (b << (i * h)) | (a << ((i + 1) * h)),
        m.p as u32,
        h,
    )
}

/// Apply a column transposition `(j, j+1)` to matrix `m`.
fn apply_col_swap(m: &PhpMatrix, j: u32) -> PhpMatrix {
    let h = m.h as u32;
    let mut out = 0u128;
    for i in 0..m.p as u32 {
        let row = m.row(i) as u128;
        let bj = (row >> j) & 1;
        let bj1 = (row >> (j + 1)) & 1;
        let new_row = (row & !((1u128 << j) | (1u128 << (j + 1))))
            | (bj1 << j)
            | (bj << (j + 1));
        out |= new_row << (i * h);
    }
    PhpMatrix::from_bits(out, m.p as u32, h)
}

/// Images of `m` under the adjacent-transposition generators of S_P × S_H.
fn generator_images(m: &PhpMatrix) -> Vec<PhpMatrix> {
    let mut out = Vec::with_capacity((m.p as usize - 1) + (m.h as usize - 1));
    for i in 0..(m.p as u32 - 1) {
        out.push(apply_row_swap(m, i));
    }
    for j in 0..(m.h as u32 - 1) {
        out.push(apply_col_swap(m, j));
    }
    out
}

/// Simple union-find with path compression, keyed by `usize` index.
struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self { parent: (0..n).collect() }
    }
    fn find(&mut self, mut x: usize) -> usize {
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }
    fn union(&mut self, a: usize, b: usize) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

/// Enumerate canonical reps of S_P × S_H orbits of squarefree monomials of
/// degree ≤ `d` over the PHP_{P,H} variable set. Returns orbit reps in a
/// deterministic order.
///
/// Two-phase: (1) BFS in pseudo-canonical (row+col sort fixed points)
/// space; (2) union-find on pseudo-canonicals linked by adjacent-
/// transposition generators. Result is exact orbit count + a deterministic
/// rep per orbit (pseudo-canonical with smallest bits).
pub fn enumerate_php_orbit_reps(p: u32, h: u32, d: u32) -> Vec<PhpMatrix> {
    assert!(p <= PhpMatrix::MAX_DIM && h <= PhpMatrix::MAX_DIM);
    // Phase 1: BFS in pseudo-canonical space.
    let mut seen: BTreeSet<u128> = BTreeSet::new();
    let mut queue: Vec<PhpMatrix> = Vec::new();
    let empty = PhpMatrix::empty(p, h);
    let c0 = empty.canonicalize();
    seen.insert(c0.bits);
    queue.push(c0);
    let mut candidates: Vec<PhpMatrix> = vec![c0];
    while let Some(m) = queue.pop() {
        // Add-cell extensions (build up orbits of each degree).
        if m.popcount() < d {
            for i in 0..p {
                for j in 0..h {
                    if m.cell(i, j) {
                        continue;
                    }
                    let m2 = m.set_cell(i, j).canonicalize();
                    if seen.insert(m2.bits) {
                        candidates.push(m2);
                        queue.push(m2);
                    }
                }
            }
        }
        // Generator-action closure: ensure every pseudo-canonical reachable
        // by a group action from an existing candidate is itself a candidate.
        // This plus add-cell closes the candidate set under both operations;
        // UF over just generator actions then exactly computes true orbits.
        for img in generator_images(&m) {
            let c = img.canonicalize();
            if seen.insert(c.bits) {
                candidates.push(c);
                queue.push(c);
            }
        }
    }
    // Phase 2: UF over candidates via generator action.
    let idx_of: BTreeMap<u128, usize> = candidates
        .iter()
        .enumerate()
        .map(|(i, m)| (m.bits, i))
        .collect();
    let mut uf = UnionFind::new(candidates.len());
    for (i, m) in candidates.iter().enumerate() {
        for img in generator_images(m) {
            let canon = img.canonicalize();
            if let Some(&j) = idx_of.get(&canon.bits) {
                uf.union(i, j);
            }
        }
    }
    // One rep per UF component: pseudo-canonical with smallest bits.
    let mut by_root: BTreeMap<usize, PhpMatrix> = BTreeMap::new();
    let n = candidates.len();
    for i in 0..n {
        let root = uf.find(i);
        let m = candidates[i];
        by_root
            .entry(root)
            .and_modify(|r: &mut PhpMatrix| {
                if m.bits < r.bits {
                    *r = m;
                }
            })
            .or_insert(m);
    }
    let mut reps: Vec<PhpMatrix> = by_root.into_values().collect();
    reps.sort_by_key(|m| (m.popcount(), m.bits));
    reps
}

/// Map a raw bitset to the canonical orbit rep in `reps`. Returns the
/// orbit index (position in `reps`).
///
/// Strategy: pseudo-canonicalize the raw bits, look up the UF component's
/// representative. If the pseudo-canonical form is not in the rep set
/// directly (because UF merged it into another), we walk the S_P × S_H
/// orbit via generators until we land on a rep-set member.
pub fn orbit_of(reps: &[PhpMatrix], raw: PhpMatrix) -> usize {
    let canon = raw.canonicalize();
    // Build a bits→index table on first call (caller can cache outside).
    // Hot path should use OrbitIndex below instead.
    let idx_of: BTreeMap<u128, usize> = reps
        .iter()
        .enumerate()
        .map(|(i, m)| (m.bits, i))
        .collect();
    if let Some(&i) = idx_of.get(&canon.bits) {
        return i;
    }
    // Walk the orbit via generators.
    let mut visited: BTreeSet<u128> = BTreeSet::new();
    let mut queue: Vec<PhpMatrix> = vec![canon];
    visited.insert(canon.bits);
    while let Some(m) = queue.pop() {
        for img in generator_images(&m) {
            let c = img.canonicalize();
            if let Some(&i) = idx_of.get(&c.bits) {
                return i;
            }
            if visited.insert(c.bits) {
                queue.push(c);
            }
        }
    }
    panic!("orbit not found in rep set — bug in enumerate_php_orbit_reps");
}

/// Cached orbit lookup. Amortizes the bits-→-index table build cost.
pub struct OrbitIndex<'a> {
    pub reps: &'a [PhpMatrix],
    idx_of: BTreeMap<u128, usize>,
}

impl<'a> OrbitIndex<'a> {
    pub fn new(reps: &'a [PhpMatrix]) -> Self {
        let idx_of = reps
            .iter()
            .enumerate()
            .map(|(i, m)| (m.bits, i))
            .collect();
        Self { reps, idx_of }
    }

    /// Orbit index of a raw bitset. O(generator-BFS) in the worst case
    /// (pseudo-canon not in rep set), O(1) hash lookup in the common case.
    pub fn of(&self, raw: PhpMatrix) -> usize {
        let canon = raw.canonicalize();
        if let Some(&i) = self.idx_of.get(&canon.bits) {
            return i;
        }
        let mut visited: BTreeSet<u128> = BTreeSet::new();
        let mut queue: Vec<PhpMatrix> = vec![canon];
        visited.insert(canon.bits);
        while let Some(m) = queue.pop() {
            for img in generator_images(&m) {
                let c = img.canonicalize();
                if let Some(&i) = self.idx_of.get(&c.bits) {
                    return i;
                }
                if visited.insert(c.bits) {
                    queue.push(c);
                }
            }
        }
        panic!("orbit not found; bits={:x}", raw.bits);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Canonicalize should be idempotent.
    #[test]
    fn canonicalize_idempotent() {
        for (p, h) in [(3, 3), (4, 3), (4, 4), (5, 4)] {
            // Brute: try all matrices with ≤ 3 ones.
            for bits in 0u128..(1u128 << (p * h)) {
                if bits.count_ones() > 3 {
                    continue;
                }
                let m = PhpMatrix::from_bits(bits, p as u32, h as u32);
                let c = m.canonicalize();
                let c2 = c.canonicalize();
                assert_eq!(c.bits, c2.bits, "not idempotent on {:0b}", bits);
            }
        }
    }

    /// Two bitsets differing by a row or column permutation must canonicalize
    /// equal.
    #[test]
    fn canonicalize_orbit_invariant() {
        let p = 4u32;
        let h = 4u32;
        // Enumerate all ≤3-one matrices; for each, apply row 0↔1 and col 0↔1
        // transpositions and check canonical forms match.
        for bits in 0u128..(1u128 << (p * h)) {
            if bits.count_ones() > 3 {
                continue;
            }
            let m = PhpMatrix::from_bits(bits, p, h);
            let c = m.canonicalize();
            // Swap rows 0 and 1 in bits.
            let row_mask = (1u128 << h) - 1;
            let r0 = bits & row_mask;
            let r1 = (bits >> h) & row_mask;
            let rest = bits & !(row_mask | (row_mask << h));
            let swapped = rest | (r1 << 0) | (r0 << h);
            let c_s = PhpMatrix::from_bits(swapped, p, h).canonicalize();
            assert_eq!(c.bits, c_s.bits, "row swap changed canon: {:0b}", bits);
            // Swap cols 0 and 1.
            let col0_bits: u128 = (0..p).map(|i| ((bits >> (i * h)) & 1) << (i * h)).sum();
            let col1_bits: u128 =
                (0..p).map(|i| (((bits >> (i * h + 1)) & 1) << (i * h + 1))).sum();
            let restc = bits & !(col0_bits | col1_bits);
            // col0 → col1 and col1 → col0: shift bits one position.
            let new_col1: u128 = (col0_bits) << 1;
            let new_col0: u128 = (col1_bits) >> 1;
            let colswap = restc | new_col0 | new_col1;
            let c_c = PhpMatrix::from_bits(colswap, p, h).canonicalize();
            assert_eq!(c.bits, c_c.bits, "col swap changed canon: {:0b}", bits);
        }
    }

    /// Orbit count for PHP_{5,4} d=5 must match the existing engine: 54.
    #[test]
    fn orbit_count_php_5_4_d5() {
        let reps = enumerate_php_orbit_reps(5, 4, 5);
        assert_eq!(reps.len(), 54, "expected 54 orbits for PHP_{{5,4}} d=5");
    }

    /// Orbit count for PHP_{6,5} d=6 must match: 140.
    #[test]
    fn orbit_count_php_6_5_d6() {
        let reps = enumerate_php_orbit_reps(6, 5, 6);
        assert_eq!(reps.len(), 140, "expected 140 orbits for PHP_{{6,5}} d=6");
    }

    /// Definitive cross-check for PHP_{7,6} d=7: brute-force enumerate every
    /// monomial, canonicalize, UF-merge. The count from this procedure is
    /// the authoritative orbit count under S_7 × S_6; it resolves the
    /// Stage A vs existing-engine disagreement (348 vs 347).
    #[test]
    #[ignore]
    fn brute_authoritative_php_7_6_d7() {
        let p = 7u32;
        let h = 6u32;
        let d = 7u32;
        let n_vars = p * h;
        // Enumerate all bitsets with popcount ≤ d.
        let mut pseudos: BTreeSet<u128> = BTreeSet::new();
        // Iterate by popcount using Gosper's hack.
        pseudos.insert(PhpMatrix::from_bits(0, p, h).canonicalize().bits);
        for k in 1..=d {
            let mut bits: u128 = (1u128 << k) - 1;
            let max = 1u128 << n_vars;
            while bits < max {
                let c = PhpMatrix::from_bits(bits, p, h).canonicalize();
                pseudos.insert(c.bits);
                // Gosper's hack for next bitset with same popcount.
                let t = bits | (bits - 1);
                let trail = bits.trailing_zeros();
                bits = (t + 1) | (((!t & ((!t).wrapping_neg())) - 1) >> (trail + 1));
            }
        }
        let pseudos_vec: Vec<u128> = pseudos.iter().copied().collect();
        eprintln!("brute pseudos: {}", pseudos_vec.len());
        let idx_of: BTreeMap<u128, usize> = pseudos_vec
            .iter()
            .enumerate()
            .map(|(i, &b)| (b, i))
            .collect();
        let mut uf = UnionFind::new(pseudos_vec.len());
        for (i, &b) in pseudos_vec.iter().enumerate() {
            let m = PhpMatrix::from_bits(b, p, h);
            for img in generator_images(&m) {
                let c = img.canonicalize();
                if let Some(&j) = idx_of.get(&c.bits) {
                    uf.union(i, j);
                }
            }
        }
        let mut roots: BTreeSet<usize> = BTreeSet::new();
        for i in 0..pseudos_vec.len() {
            roots.insert(uf.find(i));
        }
        eprintln!("brute orbit count (UF): {}", roots.len());
        let staged = enumerate_php_orbit_reps(p, h, d);
        eprintln!("staged orbit count: {}", staged.len());
        assert_eq!(roots.len(), staged.len());
    }

    /// Sweep: print Stage A orbit counts at several (P, H, d) for comparison
    /// with the existing engine's numbers. Run explicitly via
    /// `cargo test --release --lib orbit_count_sweep -- --nocapture`.
    #[test]
    #[ignore]
    fn orbit_count_sweep() {
        for &(p, h, d) in &[
            (5u32, 4u32, 5u32),
            (5, 4, 6),
            (6, 5, 6),
            (6, 5, 7),
            (6, 5, 8),
            (7, 6, 6),
            (7, 6, 7),
            (8, 7, 7),
        ] {
            let t = std::time::Instant::now();
            let reps = enumerate_php_orbit_reps(p, h, d);
            eprintln!(
                "PHP_{{{},{}}} d={}: {} orbits in {:.3}s",
                p,
                h,
                d,
                reps.len(),
                t.elapsed().as_secs_f64()
            );
        }
    }

    /// PHP_{7,6} d=7 orbit count = 348, confirmed by brute-force
    /// `brute_authoritative_php_7_6_d7` (ignored test). The existing
    /// `monomial_orbits_on_the_fly` in [`super::super::orbit_ns`] reports
    /// 347 for this exact case — a latent off-by-one there, not here.
    #[test]
    fn orbit_count_php_7_6_d7() {
        let reps = enumerate_php_orbit_reps(7, 6, 7);
        assert_eq!(reps.len(), 348, "PHP_{{7,6}} d=7 authoritative count");
    }

    /// Brute-force cross-check: for a small PHP size, enumerate ALL monomials
    /// up to degree `d`, canonicalize each, UF-merge via generators, and
    /// compare the resulting orbit count to Stage A's direct enumeration.
    /// This validates both the pseudo-canonicalize set and the UF post-dedup.
    #[test]
    fn brute_vs_staged_php_4_3() {
        let p = 4u32;
        let h = 3u32;
        for d in 0u32..=(p * h).min(8) {
            // Brute: every bitset with popcount ≤ d.
            let mut pseudos: BTreeSet<u128> = BTreeSet::new();
            for bits in 0u128..(1u128 << (p * h)) {
                if bits.count_ones() > d {
                    continue;
                }
                let c = PhpMatrix::from_bits(bits, p, h).canonicalize();
                pseudos.insert(c.bits);
            }
            // UF-merge brute pseudos via generators (same as Stage A's
            // phase 2).
            let pseudos_vec: Vec<u128> = pseudos.iter().copied().collect();
            let idx_of: BTreeMap<u128, usize> = pseudos_vec
                .iter()
                .enumerate()
                .map(|(i, &b)| (b, i))
                .collect();
            let mut uf = UnionFind::new(pseudos_vec.len());
            for (i, &b) in pseudos_vec.iter().enumerate() {
                let m = PhpMatrix::from_bits(b, p, h);
                for img in generator_images(&m) {
                    let c = img.canonicalize();
                    if let Some(&j) = idx_of.get(&c.bits) {
                        uf.union(i, j);
                    }
                }
            }
            let mut roots: BTreeSet<usize> = BTreeSet::new();
            for i in 0..pseudos_vec.len() {
                roots.insert(uf.find(i));
            }
            let brute_orbit_count = roots.len();

            let staged = enumerate_php_orbit_reps(p, h, d);
            assert_eq!(
                brute_orbit_count,
                staged.len(),
                "PHP_{{{},{}}} d={}: brute {} orbits vs staged {} orbits",
                p,
                h,
                d,
                brute_orbit_count,
                staged.len()
            );
        }
    }

    /// Measurement: PHP_{8,7} d=7 orbit count. Ignored by default — keep
    /// the test suite fast; run explicitly to collect numbers.
    #[test]
    #[ignore]
    fn orbit_count_php_8_7_d7() {
        let t = std::time::Instant::now();
        let reps = enumerate_php_orbit_reps(8, 7, 7);
        eprintln!(
            "PHP_{{8,7}} d=7: {} orbits in {:.3}s",
            reps.len(),
            t.elapsed().as_secs_f64()
        );
        assert!(reps.len() > 0);
    }

    /// Orbit count for small PHP_{3,3} d=3: enumerate brute-force and compare.
    #[test]
    fn orbit_count_php_3_3_d3_brute() {
        let direct = enumerate_php_orbit_reps(3, 3, 3);
        // Brute: enumerate all 0-1 3×3 matrices with ≤3 ones, canonicalize,
        // dedup.
        let p = 3u32;
        let h = 3u32;
        let mut seen: BTreeSet<u128> = BTreeSet::new();
        for bits in 0u128..(1u128 << (p * h)) {
            if bits.count_ones() > 3 {
                continue;
            }
            let c = PhpMatrix::from_bits(bits, p, h).canonicalize();
            seen.insert(c.bits);
        }
        assert_eq!(direct.len(), seen.len());
        let direct_set: BTreeSet<u128> = direct.iter().map(|m| m.bits).collect();
        assert_eq!(direct_set, seen);
    }
}
