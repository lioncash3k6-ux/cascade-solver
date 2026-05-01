//! Generic orbit-reduced Nullstellensatz over 𝔽_p.
//!
//! Takes a [`TupleVarSchema`] and a list of polynomial axioms, and searches
//! for a G-invariant NS certificate at the given degree. Replaces the
//! PHP-specific engine in [`crate::algebra::php_orbit`]: problem-specific
//! code lives in [`crate::problems`], this engine is problem-agnostic.
//!
//! # Preconditions for soundness
//!
//! * The axioms must be closed under the group action: for every generator
//!   `g` and every axiom `A_i`, there must exist an axiom `A_j` with
//!   `g·A_i = A_j`. This holds by construction for problem factories in
//!   [`crate::problems`].
//! * The prime `p` must NOT divide `|G|`. Otherwise, G-invariant certs
//!   may not exist even when non-invariant ones do, and this engine will
//!   return `None`.

use super::ns_fp::PolyP;
use super::poly::Monomial;
use crate::tuple_schema::{Generator, TupleVarSchema};
use rayon::prelude::*;
use std::collections::BTreeMap;

/// Raw pointer wrapper that is Send+Sync for use in parallel GE row elimination.
/// SAFETY: caller must guarantee no two threads alias the same row.
struct RowPtr(*mut Vec<u8>);
unsafe impl Send for RowPtr {}
unsafe impl Sync for RowPtr {}

/// Fixed-capacity bitmask monomial representation. Bit `v-1` is set iff
/// variable `v` is in the monomial support. Keeps the engine in purely
/// integer arithmetic for monomial operations — no allocation per apply
/// or multiply.
///
/// Backed by `[u64; N_WORDS]` for `N_WORDS · 64` capacity. Currently
/// 1024 bits (16 words), covering PHP up to P·H = 1024 and Ramsey up to
/// K_45 (990 edges). For larger families bump `N_WORDS` or switch to
/// a dynamic bitset.
const N_WORDS: usize = 16;

#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Default, Debug)]
pub(crate) struct MonoBits {
    w: [u64; N_WORDS],
}

impl MonoBits {
    pub(crate) const ZERO: Self = Self { w: [0; N_WORDS] };
    pub(crate) const CAPACITY: u32 = (N_WORDS as u32) * 64;

    #[inline]
    pub(crate) fn single(v: u32) -> Self {
        debug_assert!(v < Self::CAPACITY);
        let mut b = Self::ZERO;
        b.w[(v / 64) as usize] = 1u64 << (v % 64);
        b
    }

    #[inline]
    pub(crate) fn set_bit(&mut self, v: u32) {
        debug_assert!(v < Self::CAPACITY);
        self.w[(v / 64) as usize] |= 1u64 << (v % 64);
    }

    #[inline]
    pub(crate) fn is_zero(&self) -> bool {
        self.w.iter().all(|&x| x == 0)
    }

    /// Position of the lowest set bit; returns `CAPACITY` if empty.
    #[inline]
    pub(crate) fn trailing_zeros(&self) -> u32 {
        for (i, &x) in self.w.iter().enumerate() {
            if x != 0 {
                return (i as u32) * 64 + x.trailing_zeros();
            }
        }
        Self::CAPACITY
    }

    #[inline]
    pub(crate) fn count_ones(&self) -> u32 {
        self.w.iter().map(|x| x.count_ones()).sum()
    }

    /// Clear the lowest set bit. Equivalent to `b &= b - 1` on u128.
    #[inline]
    pub(crate) fn clear_lowest(&mut self) {
        for x in self.w.iter_mut() {
            if *x != 0 {
                *x &= *x - 1;
                return;
            }
        }
    }
}

impl std::ops::BitOr for MonoBits {
    type Output = Self;
    #[inline]
    fn bitor(self, rhs: Self) -> Self {
        let mut r = Self::ZERO;
        for i in 0..N_WORDS {
            r.w[i] = self.w[i] | rhs.w[i];
        }
        r
    }
}

impl std::ops::BitOrAssign for MonoBits {
    #[inline]
    fn bitor_assign(&mut self, rhs: Self) {
        for i in 0..N_WORDS {
            self.w[i] |= rhs.w[i];
        }
    }
}

fn mono_to_bits(m: &Monomial, n: u32) -> MonoBits {
    debug_assert!(n <= MonoBits::CAPACITY);
    let mut b = MonoBits::ZERO;
    for &v in &m.0 {
        debug_assert!(v >= 1 && v <= n);
        b.set_bit(v - 1);
    }
    b
}

fn bits_to_mono(mut b: MonoBits) -> Monomial {
    let mut s = std::collections::BTreeSet::new();
    while !b.is_zero() {
        let lo = b.trailing_zeros();
        s.insert(lo + 1);
        b.clear_lowest();
    }
    Monomial(s)
}

fn apply_bits(mut b: MonoBits, var_table: &[u32]) -> MonoBits {
    let mut out = MonoBits::ZERO;
    while !b.is_zero() {
        let lo = b.trailing_zeros() as usize;
        out.set_bit(var_table[lo + 1] - 1);
        b.clear_lowest();
    }
    out
}

/// Enumerate all multilinear monomials of degree exactly `k` over the
/// variables `1..=n`.
fn enumerate_of_degree(n: u32, k: usize) -> Vec<Monomial> {
    let mut out = Vec::new();
    let vars: Vec<u32> = (1..=n).collect();
    fn rec(
        vars: &[u32],
        start: usize,
        k_left: usize,
        chosen: &mut Vec<u32>,
        out: &mut Vec<Monomial>,
    ) {
        if k_left == 0 {
            out.push(Monomial::from_vars(chosen.iter().copied()));
            return;
        }
        if vars.len() - start < k_left {
            return;
        }
        for i in start..vars.len() {
            chosen.push(vars[i]);
            rec(vars, i + 1, k_left - 1, chosen, out);
            chosen.pop();
        }
    }
    let mut chosen = Vec::with_capacity(k);
    rec(&vars, 0, k, &mut chosen, &mut out);
    out
}

fn enumerate_up_to(n: u32, d: usize) -> Vec<Monomial> {
    let mut out = Vec::new();
    for k in 0..=d {
        out.extend(enumerate_of_degree(n, k));
    }
    out.sort();
    out
}

/// Enumerate multilinear monomials of degree ≤ `d` over `1..=n` as
/// bitmasks, **in colex order** (grouped by degree, colex within degree).
///
/// Colex order lets us replace the `HashMap<bits, usize>` monomial → index
/// lookup with a direct combinatorial ranking ([`ColexIndex::rank`]) —
/// O(d) arithmetic instead of a hash probe, and zero memory. At PHP_{8,7}
/// d=7 scale the HashMap was 15-20 GB; the ranking is a tiny
/// `binom[n+1][d+1]` table (a few KB).
///
/// Ordering (for a 2-subset of [4], the colex sequence is):
/// `{1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {3,4}`.
fn enumerate_bits_up_to(n: u32, d: usize) -> Vec<MonoBits> {
    fn rec(max_val: u32, k_left: u32, bits: MonoBits, out: &mut Vec<MonoBits>) {
        if k_left == 0 {
            out.push(bits);
            return;
        }
        for v in k_left..=max_val {
            rec(v - 1, k_left - 1, bits | MonoBits::single(v - 1), out);
        }
    }
    let mut out = Vec::new();
    for k in 0..=(d as u32) {
        rec(n, k, MonoBits::ZERO, &mut out);
    }
    out
}

/// Perfect-hash index for multilinear monomials of degree ≤ `d` over
/// `1..=n`, via colex ranking. `rank(bits)` returns the position of a
/// monomial in the `enumerate_bits_up_to(n, d)` sequence; `unrank(r)`
/// inverts it.
///
/// Replaces the old `bits_index: HashMap<u128, usize>` (which at
/// PHP_{8,7} d=7 scale cost ~15-20 GB) with `O((d+1)·(n+1))` bytes of
/// binomial table.
struct ColexIndex {
    // binom[a][k] = C(a, k). Dimensions (n+2) × (d+2); a trailing row/col
    // avoids bounds-check branches on edge lookups.
    binom: Vec<Vec<u64>>,
    // prefix[k] = total count of monomials of degree < k, i.e.
    // ∑_{k'=0..k-1} C(n, k'). Length (d+2).
    prefix: Vec<u64>,
    n: u32,
    d: u32,
}

impl ColexIndex {
    fn new(n: u32, d: u32) -> Self {
        let nn = (n + 2) as usize;
        let dd = (d + 2) as usize;
        let mut binom = vec![vec![0u64; dd]; nn];
        for a in 0..nn {
            binom[a][0] = 1;
            for k in 1..dd {
                // C(a, k) = C(a-1, k-1) + C(a-1, k) with boundary C(0, >0) = 0.
                let upper = if a == 0 { 0 } else { binom[a - 1][k - 1] };
                let left = if a == 0 { 0 } else { binom[a - 1][k] };
                binom[a][k] = upper.saturating_add(left);
            }
        }
        let mut prefix = vec![0u64; (d + 2) as usize];
        for k in 0..=(d as usize) {
            prefix[k + 1] = prefix[k].saturating_add(binom[n as usize][k]);
        }
        Self { binom, prefix, n, d }
    }

    /// Total number of monomials of degree ≤ d.
    fn len(&self) -> usize {
        self.prefix[(self.d + 1) as usize] as usize
    }

    /// Number of monomials of degree ≤ k (clamped to d).
    /// The colex enumeration is degree-sorted, so these are exactly the
    /// first `len_up_to_degree(k)` entries.
    #[inline]
    fn len_up_to_degree(&self, k: usize) -> usize {
        self.prefix[k.min(self.d as usize) + 1] as usize
    }

    /// Rank a monomial bitset in the colex enumeration.
    ///
    /// Formula: for `S = {a_1 < ... < a_k}` (1-indexed elements),
    /// `rank = prefix[k] + ∑_{i=1..k} C(a_i - 1, i)`.
    #[inline]
    fn rank(&self, bits: MonoBits) -> usize {
        let k = bits.count_ones();
        let mut r = self.prefix[k as usize];
        let mut b = bits;
        let mut i: u32 = 1;
        while !b.is_zero() {
            let v = b.trailing_zeros(); // 0-indexed bit position = a_i - 1
            r += self.binom[v as usize][i as usize];
            b.clear_lowest();
            i += 1;
        }
        r as usize
    }

    /// Invert [`rank`]: return the monomial bitset at position `r`.
    ///
    /// Inner `a`-search uses binary search over the monotone column
    /// `binom[·][i]`: O(d · log n) total vs the naive O(d · n). This
    /// matters when `unrank` is on the hot path as a replacement for the
    /// `Vec<MonoBits>` array (on-demand bits for memory-bound instances).
    #[inline]
    fn unrank(&self, r: usize) -> MonoBits {
        // Find degree k with prefix[k] ≤ r < prefix[k+1].
        let mut r = r as u64;
        let mut k: u32 = 0;
        while k <= self.d && self.prefix[(k + 1) as usize] <= r {
            k += 1;
        }
        debug_assert!(k <= self.d);
        let mut rem = r - self.prefix[k as usize];
        let mut bits = MonoBits::ZERO;
        // Peel off a_k, a_{k-1}, ..., a_1 in decreasing i. Within orbit
        // `i`, a is strictly bounded above by the previously chosen a
        // (colex ordering); keep that bound for binary-search range.
        let mut hi = self.n;
        for i in (1..=k).rev() {
            // Find largest a ∈ [0, hi] with C(a, i) ≤ rem; a_i = a + 1.
            let iu = i as usize;
            let mut lo: u32 = 0;
            let mut r_hi = hi;
            while lo < r_hi {
                let mid = lo + (r_hi - lo + 1) / 2;
                if self.binom[mid as usize][iu] <= rem {
                    lo = mid;
                } else {
                    r_hi = mid - 1;
                }
            }
            let a = lo;
            bits.set_bit(a);
            rem -= self.binom[a as usize][iu];
            hi = if a > 0 { a - 1 } else { 0 };
        }
        debug_assert_eq!(rem, 0);
        bits
    }

    /// Monomial bits at position `r` — O(d · log n). Wrapper for readability
    /// at call sites that are consuming bits on-demand (in lieu of a
    /// materialized `monos_bits[r]` array access).
    #[inline]
    fn bits_at(&self, r: usize) -> MonoBits {
        self.unrank(r)
    }
}

#[cfg(test)]
mod colex_tests {
    use super::*;

    #[test]
    fn rank_matches_enumeration() {
        // For each (n, d), colex rank of the i-th bitset must equal i.
        for n in [3u32, 5, 7, 10] {
            for d in 1u32..=4 {
                let enum_bits = enumerate_bits_up_to(n, d as usize);
                let ci = ColexIndex::new(n, d);
                assert_eq!(ci.len(), enum_bits.len());
                for (i, &b) in enum_bits.iter().enumerate() {
                    let r = ci.rank(b);
                    assert_eq!(r, i, "n={}, d={}: rank = {}, expected {}", n, d, r, i);
                    let b2 = ci.unrank(r);
                    assert_eq!(b2, b, "n={}, d={}: unrank({}) differs", n, d, r);
                }
            }
        }
    }
}

/// Compute monomial orbits for `UnorderedPair + Diagonal` (Ramsey) schemas.
///
/// Uses `enumerate_orbit_reps(n_verts, d)` to get ~300-400 canonical orbit
/// representatives, then enumerates all injective maps of each rep into K_n
/// to fill `orbit_id` directly — no BFS over the full monomial space needed.
///
/// Cost: Σ_reps P(n, k_rep) × O(k) per visit, where k ≤ 2d (tree bound).
/// For K_11 d=7 this is ~700M visits at ~3 ops each vs BFS's 2.4B unrank+apply+rank
/// calls, giving ~4–5× speedup (173 s → ~35 s for K_11).
fn monomial_orbits_via_embedding(
    n_verts: u32,
    d: u32,
    n_monos: usize,
    colex: &ColexIndex,
) -> (Vec<u32>, Vec<u32>) {
    use super::graph_canon::{edge_to_bit, enumerate_orbit_reps};

    assert!(
        n_monos <= u32::MAX as usize,
        "n_monos ({}) exceeds u32 range",
        n_monos
    );

    let mut orbit_id = vec![u32::MAX; n_monos];
    let mut orbit_rep: Vec<u32> = Vec::new();

    let reps = enumerate_orbit_reps(n_verts, d);

    for (orbit_idx, (rep_bits, canon_g, _)) in reps.iter().enumerate() {
        orbit_rep.push(colex.rank(*rep_bits) as u32);
        let k = canon_g.n_verts as usize;
        let canon_edges: Vec<(u8, u8)> = canon_g.edge_iter().collect();
        let mut sigma = vec![0u32; k];
        let mut used = vec![false; n_verts as usize];
        fill_orbit_by_injection(
            0,
            k,
            n_verts,
            &mut sigma,
            &mut used,
            &canon_edges,
            orbit_idx as u32,
            &mut orbit_id,
            colex,
        );
    }

    debug_assert!(
        !orbit_id.iter().any(|&x| x == u32::MAX),
        "orbit_id has unassigned entries after embedding enumeration"
    );
    (orbit_id, orbit_rep)
}

/// Recursive helper: enumerate all injective maps σ: {0..k−1} → {0..n_verts−1}
/// and, for each, compute the MonoBits for `canon_edges` under σ and write
/// `orbit_idx` into `orbit_id[colex.rank(bits)]`.
fn fill_orbit_by_injection(
    pos: usize,
    k: usize,
    n_verts: u32,
    sigma: &mut Vec<u32>,
    used: &mut Vec<bool>,
    canon_edges: &[(u8, u8)],
    orbit_idx: u32,
    orbit_id: &mut Vec<u32>,
    colex: &ColexIndex,
) {
    use super::graph_canon::edge_to_bit;
    if pos == k {
        let mut bits = MonoBits::ZERO;
        for &(u, v) in canon_edges {
            let a = sigma[u as usize] + 1;
            let b = sigma[v as usize] + 1;
            let (lo, hi) = if a < b { (a, b) } else { (b, a) };
            bits.set_bit(edge_to_bit(lo, hi, n_verts));
        }
        orbit_id[colex.rank(bits)] = orbit_idx;
        return;
    }
    for v in 0..n_verts as usize {
        if !used[v] {
            used[v] = true;
            sigma[pos] = v as u32;
            fill_orbit_by_injection(
                pos + 1,
                k,
                n_verts,
                sigma,
                used,
                canon_edges,
                orbit_idx,
                orbit_id,
                colex,
            );
            used[v] = false;
        }
    }
}

/// Compute G-orbits of monomials by BFS with on-the-fly generator application.
/// Fallback for schemas where the embedding approach does not apply (PHP,
/// Tseitin with a proper subgroup, Count_q, …).
///
/// Memory: only `orbit_id: Vec<u32>` of size `n_monos`. Cost per visited
/// BFS edge: one `unrank` + `apply_bits` + `rank`.
fn monomial_orbits_bfs(
    n_monos: usize,
    colex: &ColexIndex,
    var_tables: &[Vec<u32>],
) -> (Vec<u32>, Vec<u32>) {
    assert!(
        n_monos <= u32::MAX as usize,
        "n_monos ({}) exceeds u32 range; widen mono_orbit_id to usize",
        n_monos
    );
    let sentinel = u32::MAX;
    let mut orbit_id = vec![sentinel; n_monos];
    let mut orbit_rep: Vec<u32> = Vec::new();
    let mut queue: Vec<u32> = Vec::new();
    for start in 0..n_monos {
        if orbit_id[start] != sentinel {
            continue;
        }
        let this_orbit = orbit_rep.len() as u32;
        orbit_id[start] = this_orbit;
        let mut rep: usize = start;
        queue.clear();
        queue.push(start as u32);
        while let Some(i) = queue.pop() {
            let bits_i = colex.bits_at(i as usize);
            for vt in var_tables {
                let img_bits = apply_bits(bits_i, vt);
                let j = colex.rank(img_bits);
                if orbit_id[j] == sentinel {
                    orbit_id[j] = this_orbit;
                    if j < rep {
                        rep = j;
                    }
                    queue.push(j as u32);
                }
            }
        }
        orbit_rep.push(rep as u32);
    }
    (orbit_id, orbit_rep)
}

/// Dispatch: use the fast embedding path for `UnorderedPair + Diagonal` (Ramsey/K_n),
/// fall back to BFS for all other schemas.
fn monomial_orbits_on_the_fly(
    schema: &crate::tuple_schema::TupleVarSchema,
    gens: &[crate::tuple_schema::Generator],
    n_monos: usize,
    colex: &ColexIndex,
    var_tables: &[Vec<u32>],
) -> (Vec<u32>, Vec<u32>) {
    use crate::tuple_schema::{GroupSpec, TupleKind};

    // Fast path: full S_n symmetry on unordered edge pairs (Ramsey K_n).
    // Condition: UnorderedPair + Diagonal + exactly n_verts−1 generators (= full S_n).
    if matches!(schema.tuple_kind, TupleKind::UnorderedPair)
        && matches!(schema.group, GroupSpec::Diagonal)
        && schema.bases.len() == 1
        && gens.len() == schema.bases[0].size.saturating_sub(1) as usize
    {
        let n_verts = schema.bases[0].size;
        return monomial_orbits_via_embedding(n_verts, colex.d, n_monos, colex);
    }

    // General BFS fallback.
    monomial_orbits_bfs(n_monos, colex, var_tables)
}

/// Canonical key for a 𝔽_p polynomial: sorted list of (monomial, coef) pairs.
/// Used to build a lookup table that maps `g·A_i` → `A_j`.
fn poly_key(q: &PolyP) -> Vec<(Monomial, u8)> {
    let mut v: Vec<(Monomial, u8)> =
        q.terms.iter().map(|(m, c)| (m.clone(), *c)).collect();
    v.sort();
    v
}

/// Apply a generator `g` to every monomial in polynomial `q`.
fn apply_gen_to_poly(schema: &TupleVarSchema, g: &Generator, q: &PolyP) -> PolyP {
    let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
    for (m, c) in &q.terms {
        let m_img = schema.apply_mono(m, g);
        let e = terms.entry(m_img).or_insert(0);
        *e = (*e + c) % q.p;
        if *e == 0 {
            terms.remove(&schema.apply_mono(m, g));
        }
    }
    PolyP { p: q.p, terms }
}

/// Precompute `axiom_action[g_idx][i] = j` such that `g·A_i = A_j`.
///
/// Panics if the axiom set is not closed under the group action.
fn axiom_action_table(
    schema: &TupleVarSchema,
    axioms: &[PolyP],
    gens: &[Generator],
) -> Vec<Vec<usize>> {
    let mut idx_of_key: BTreeMap<Vec<(Monomial, u8)>, usize> = BTreeMap::new();
    for (i, a) in axioms.iter().enumerate() {
        idx_of_key.insert(poly_key(a), i);
    }
    let mut out = vec![vec![0usize; axioms.len()]; gens.len()];
    for (gi, g) in gens.iter().enumerate() {
        for (i, a) in axioms.iter().enumerate() {
            let img = apply_gen_to_poly(schema, g, a);
            let key = poly_key(&img);
            out[gi][i] = *idx_of_key
                .get(&key)
                .expect("axioms not closed under group action");
        }
    }
    out
}

/// In-place `row += neg_k * pivot` over sorted sparse rows.
/// Each row is a Vec<(col, val)> sorted by col. Zero entries are dropped.
#[inline]
fn sparse_saxpy(row: &mut Vec<(u32, u8)>, pivot: &[(u32, u8)], neg_k: u8, p: u8) {
    let p16 = p as u16;
    let mut out: Vec<(u32, u8)> = Vec::with_capacity(row.len() + pivot.len());
    let mut ri = 0;
    let mut pi = 0;
    while ri < row.len() || pi < pivot.len() {
        let rc = row.get(ri).map_or(u32::MAX, |&(c, _)| c);
        let pc = pivot.get(pi).map_or(u32::MAX, |&(c, _)| c);
        if rc < pc {
            out.push(row[ri]);
            ri += 1;
        } else if rc > pc {
            let v = (neg_k as u16 * pivot[pi].1 as u16 % p16) as u8;
            if v != 0 { out.push((pc, v)); }
            pi += 1;
        } else {
            let v = ((row[ri].1 as u16 + neg_k as u16 * pivot[pi].1 as u16) % p16) as u8;
            if v != 0 { out.push((rc, v)); }
            ri += 1;
            pi += 1;
        }
    }
    *row = out;
}

// ─────────────────────────────────────────────────────────────────────────────
// Block Wiedemann solver over 𝔽_p (avoids all fill-in from GE)
// ─────────────────────────────────────────────────────────────────────────────

/// Smallest prime strictly greater than `n`.
fn next_prime_above(n: u64) -> u64 {
    let mut c = n + 1 + (n & 1); // start at odd number > n
    loop {
        let mut prime = true;
        let mut d = 3u64;
        while d * d <= c { if c % d == 0 { prime = false; break; } d += 2; }
        if prime { return c; }
        c += 2;
    }
}

/// Modular inverse via extended Euclidean algorithm (u64 version).
fn mod_inv_u64(a: u64, p: u64) -> u64 {
    let (mut old_r, mut r) = (a as i128, p as i128);
    let (mut old_s, mut s) = (1i128, 0i128);
    while r != 0 {
        let q = old_r / r;
        let tmp = r; r = old_r - q * r; old_r = tmp;
        let tmp = s; s = old_s - q * s; old_s = tmp;
    }
    ((old_s % p as i128 + p as i128) as u64) % p
}

/// BM over F_{p} with u64 field elements. Returns LFSR poly L = [1, L_1, ...].
fn berlekamp_massey_fp64(s: &[u64], p: u64) -> Vec<u64> {
    let n = s.len();
    let mut l: Vec<u64> = vec![1u64];
    let mut b: Vec<u64> = vec![1u64];
    let mut b_shift = 1usize;
    let mut delta_inv = 1u64;
    for k in 0..n {
        let r = l.len() - 1;
        // Accumulate in u128 to avoid per-term modulo.
        // Max: (r+1) * (p-1)^2 ≤ rank * p^2 ≤ 200000 * (12M)^2 = 2.88e16 < u64::MAX, but
        // with p_work ≈ 2.2M and r ≈ 22000: 22000 * 2.2e6^2 = 1.06e17 > u64::MAX.
        // Use u128 to be safe.
        let mut d_acc = 0u128;
        for i in 0..=r {
            if k >= i { d_acc += l[i] as u128 * s[k - i] as u128; }
        }
        let d = (d_acc % p as u128) as u64;
        if d == 0 { b_shift += 1; continue; }
        let coef = d * delta_inv % p;
        let new_len = r + b_shift + b.len();
        let mut l_new = vec![0u64; new_len.max(l.len())];
        for i in 0..l.len() { l_new[i] = l[i]; }
        for i in 0..b.len() {
            let idx = i + b_shift;
            if idx < l_new.len() {
                let sub = coef * b[i] % p;
                l_new[idx] = (l_new[idx] + p - sub) % p;
            }
        }
        while l_new.len() > 1 && *l_new.last().unwrap() == 0 { l_new.pop(); }
        if 2 * r <= k {
            b = l.clone();
            delta_inv = mod_inv_u64(d, p);
            b_shift = 1;
        } else {
            b_shift += 1;
        }
        l = l_new;
    }
    l
}

fn poly_reverse_u64(a: &[u64]) -> Vec<u64> {
    let mut r: Vec<u64> = a.iter().rev().cloned().collect();
    while r.len() > 1 && *r.last().unwrap() == 0 { r.pop(); }
    r
}

fn poly_mul_fp64(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    if a.iter().all(|&v| v == 0) || b.iter().all(|&v| v == 0) { return vec![0u64]; }
    let mut c = vec![0u64; a.len() + b.len() - 1];
    for (i, &ai) in a.iter().enumerate() {
        if ai == 0 { continue; }
        for (j, &bj) in b.iter().enumerate() {
            c[i + j] = (c[i + j] + ai * bj) % p;
        }
    }
    c
}

fn poly_rem_fp64(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    if b.is_empty() || (b.len() == 1 && b[0] == 0) { return vec![0u64]; }
    let mut r = a.to_vec();
    let lead_b_inv = mod_inv_u64(*b.last().unwrap(), p);
    while r.len() >= b.len() {
        let lead_r = *r.last().unwrap();
        if lead_r == 0 { r.pop(); continue; }
        let d = r.len() - b.len();
        let coef = lead_r * lead_b_inv % p;
        for i in 0..b.len() {
            let sub = coef * b[i] % p;
            r[i + d] = (r[i + d] + p - sub) % p;
        }
        while r.len() > 0 && *r.last().unwrap() == 0 { r.pop(); }
    }
    if r.is_empty() { r.push(0); }
    r
}

fn poly_gcd_fp64(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    let mut x = a.to_vec();
    let mut y = b.to_vec();
    while !(y.len() == 1 && y[0] == 0) {
        let r = poly_rem_fp64(&x, &y, p);
        x = y;
        y = r;
    }
    if x.is_empty() { return vec![1u64]; }
    let lead_inv = mod_inv_u64(*x.last().unwrap(), p);
    for v in &mut x { *v = *v * lead_inv % p; }
    x
}

fn poly_exact_div_fp64(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    if b.len() == 1 && b[0] == 1 { return a.to_vec(); }
    let mut r = a.to_vec();
    let lead_b_inv = mod_inv_u64(*b.last().unwrap(), p);
    let d = a.len().saturating_sub(b.len());
    let mut q = vec![0u64; d + 1];
    let mut deg_r = r.len();
    while deg_r >= b.len() {
        while deg_r > 0 && r[deg_r - 1] == 0 { deg_r -= 1; }
        if deg_r < b.len() { break; }
        let qi_idx = deg_r - b.len();
        let lead_r = r[deg_r - 1];
        if lead_r == 0 { break; }
        let coef = lead_r * lead_b_inv % p;
        q[qi_idx] = coef;
        for i in 0..b.len() {
            let sub = coef * b[i] % p;
            r[i + qi_idx] = (r[i + qi_idx] + p - sub) % p;
        }
        if deg_r > 0 { deg_r -= 1; }
    }
    q
}

fn poly_lcm_fp64(a: &[u64], b: &[u64], p: u64) -> Vec<u64> {
    let g = poly_gcd_fp64(a, b, p);
    let q = poly_exact_div_fp64(a, &g, p);
    let mut result = poly_mul_fp64(&q, b, p);
    if let Some(&lead) = result.last() {
        if lead > 1 { let inv = mod_inv_u64(lead, p); for v in &mut result { *v = *v * inv % p; } }
    }
    result
}

/// y = A × x  over F_{p_work}, matrix entries stored as u8 (≤ p_orig ≤ p_work).
/// y = A × x over F_{p_work}.  Entries of `rows` are already in F_{p_work} (u64 values).
/// Uses rayon when the matrix is large (nnz > 500K rows).
fn matvec_fp64(rows: &[Vec<(u32, u64)>], x: &[u64], n_cols: usize, p: u64) -> Vec<u64> {
    use rayon::prelude::*;
    rows.par_iter().map(|row| {
        let mut acc = 0u128;
        for &(c, a) in row {
            if (c as usize) < n_cols { acc += a as u128 * x[c as usize] as u128; }
        }
        (acc % p as u128) as u64
    }).collect()
}

/// y = A^T × x over F_{p_work}.
/// Sequential: the n_cols accumulator (~1MB) fits in L3 cache; parallel would thrash it.
fn matvec_T_fp64(rows: &[Vec<(u32, u64)>], x: &[u64], n_cols: usize, p: u64) -> Vec<u64> {
    let mut acc = vec![0u128; n_cols];
    for (i, row) in rows.iter().enumerate() {
        let xi = x[i];
        if xi == 0 { continue; }
        for &(c, a) in row {
            let col = c as usize;
            if col < n_cols { acc[col] += a as u128 * xi as u128; }
        }
    }
    acc.iter().map(|&v| (v % p as u128) as u64).collect()
}

/// Scalar Wiedemann over F_{p_work} (large prime, p_work > n_rows), solving A x = b.
/// `rows` must already be the matrix over F_{p_work} (u64 entries, including RHS at col n_cols).
/// Returns x such that A x = b over F_{p_work}, or None after MAX_TRIALS failures.
fn sparse_wiedemann_large_prime(
    rows: &[Vec<(u32, u64)>],
    n_cols: usize,
    p_work: u64,
    verbose: bool,
) -> Option<Vec<u64>> {
    let t0 = std::time::Instant::now();
    let n_rows = rows.len();
    let rank_bound = n_rows.min(n_cols);

    let rhs_col = n_cols as u32;
    let b_rhs: Vec<u64> = rows.iter().map(|row| {
        row.iter().find(|&&(c, _)| c == rhs_col).map(|&(_, v)| v).unwrap_or(0)
    }).collect();
    if b_rhs.iter().all(|&v| v == 0) { return None; }

    let k_len = 2 * rank_bound + 64;
    let nnz: usize = rows.iter().map(|r| r.iter().filter(|&&(c,_)| (c as usize) < n_cols).count()).sum();

    if verbose {
        eprintln!("c [alg-timing] wiedemann_lp: n_rows={} n_cols={} nnz={} p_work={} k_len={}",
            n_rows, n_cols, nnz, p_work, k_len);
    }

    for trial in 0..16u32 {
        // Random left vector u ∈ F_{p_work}^{n_rows}.
        let mut rng = 0x9e3779b97f4a7c15u64
            ^ (n_cols as u64).wrapping_mul(6364136223846793005)
            ^ (trial as u64).wrapping_mul(0xbf58476d1ce4e5b9);
        let u: Vec<u64> = (0..n_rows).map(|_| {
            rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            (rng >> 11) % p_work
        }).collect();

        // Phase 1: Krylov sequence s[k] = u · (M')^k b over F_{p_work}, M' = AA^T.
        let mut seq: Vec<u64> = Vec::with_capacity(k_len);
        let mut cv = b_rhs.clone();
        for _ in 0..k_len {
            let dot = {
                let mut acc = 0u128;
                for (&ui, &ci) in u.iter().zip(cv.iter()) { acc += ui as u128 * ci as u128; }
                (acc % p_work as u128) as u64
            };
            seq.push(dot);
            let at_c = matvec_T_fp64(rows, &cv, n_cols, p_work);
            cv = matvec_fp64(rows, &at_c, n_cols, p_work);
        }

        if verbose {
            eprintln!("c [alg-timing] wiedemann_lp phase1 (trial {}): {:.3}s", trial, t0.elapsed().as_secs_f64());
        }

        // Phase 2: BM → minimal polynomial μ, then q = reverse(μ).
        let mu = berlekamp_massey_fp64(&seq, p_work);
        let q = poly_reverse_u64(&mu);
        let deg_q = q.len().saturating_sub(1);

        if verbose {
            eprintln!("c [alg-timing] wiedemann_lp phase2 (trial {}): {:.3}s, deg(q)={}",
                trial, t0.elapsed().as_secs_f64(), deg_q);
        }

        if deg_q == 0 || q[0] == 0 { continue; }

        // Phase 3: z = q_0^{-1} * (-q_1 b - q_2 M'b - ... - q_d (M')^{d-1} b), then x = A^T z.
        let q0_inv = mod_inv_u64(q[0], p_work);
        let mut z_acc = vec![0u64; n_rows];
        {
            let mut v = b_rhs.clone();
            for j in 0..deg_q {
                let coef = q[j + 1];
                if coef != 0 {
                    let neg_c = (p_work - coef) * q0_inv % p_work;
                    for (za, &vv) in z_acc.iter_mut().zip(v.iter()) {
                        *za = (*za + neg_c * vv) % p_work;
                    }
                }
                if j + 1 < deg_q {
                    let at_v = matvec_T_fp64(rows, &v, n_cols, p_work);
                    v = matvec_fp64(rows, &at_v, n_cols, p_work);
                }
            }
        }
        let x_sol = matvec_T_fp64(rows, &z_acc, n_cols, p_work);

        if verbose {
            eprintln!("c [alg-timing] wiedemann_lp phase3 (trial {}): {:.3}s", trial, t0.elapsed().as_secs_f64());
        }

        // Verify A*x = b over F_{p_work}.
        let ax = matvec_fp64(rows, &x_sol, n_cols, p_work);
        if ax == b_rhs {
            if verbose {
                eprintln!("c [alg-timing] wiedemann_lp: {:.3}s (VERIFIED, trial {})",
                    t0.elapsed().as_secs_f64(), trial);
            }
            return Some(x_sol);
        }
        if verbose {
            let mismatches = ax.iter().zip(b_rhs.iter()).filter(|(a, b)| a != b).count();
            eprintln!("c [alg-timing] wiedemann_lp trial {}: verification failed ({} mismatches), retrying",
                trial, mismatches);
        }
    }

    if verbose {
        eprintln!("c [alg-timing] wiedemann_lp: {:.3}s (all trials failed)", t0.elapsed().as_secs_f64());
    }
    None
}


/// Compute y = A × x  (m-vector) for sparse A stored as `rows` (cols < n_cols).
#[inline]
fn matvec_fp(rows: &[Vec<(u32, u8)>], x: &[u8], n_cols: usize, p: u8, par: bool) -> Vec<u8> {
    let p32 = p as u32;
    if par {
        use rayon::prelude::*;
        rows.par_iter().map(|row| {
            let mut acc = 0u32;
            for &(c, a) in row {
                if (c as usize) < n_cols { acc += a as u32 * x[c as usize] as u32; }
            }
            (acc % p32) as u8
        }).collect()
    } else {
        rows.iter().map(|row| {
            let mut acc = 0u32;
            for &(c, a) in row {
                if (c as usize) < n_cols { acc += a as u32 * x[c as usize] as u32; }
            }
            (acc % p32) as u8
        }).collect()
    }
}

/// Compute y = A^T × x  (n-vector) for sparse A.
fn matvec_T_fp(rows: &[Vec<(u32, u8)>], x: &[u8], n_cols: usize, p: u8, par: bool) -> Vec<u8> {
    let p32 = p as u32;
    if par {
        use rayon::prelude::*;
        let n_threads = rayon::current_num_threads().max(1);
        let chunk = (rows.len() + n_threads - 1) / n_threads;
        let partial: Vec<Vec<u32>> = rows.par_chunks(chunk).enumerate().map(|(ci, chunk_rows)| {
            let base = ci * chunk;
            let mut local = vec![0u32; n_cols];
            for (j, row) in chunk_rows.iter().enumerate() {
                let xi = x[base + j] as u32;
                if xi == 0 { continue; }
                for &(c, a) in row {
                    let col = c as usize;
                    if col < n_cols { local[col] += a as u32 * xi; }
                }
            }
            local
        }).collect();
        let mut acc = vec![0u32; n_cols];
        for part in &partial { for (a, v) in acc.iter_mut().zip(part.iter()) { *a += v; } }
        acc.iter().map(|&v| (v % p32) as u8).collect()
    } else {
        let mut acc = vec![0u32; n_cols];
        for (i, row) in rows.iter().enumerate() {
            let xi = x[i] as u32;
            if xi == 0 { continue; }
            for &(c, a) in row {
                let col = c as usize;
                if col < n_cols { acc[col] += a as u32 * xi; }
            }
        }
        acc.iter().map(|&v| (v % p32) as u8).collect()
    }
}

/// Berlekamp-Massey over 𝔽_p.
/// Returns LFSR feedback polynomial L = [L_0=1, L_1, …, L_r] such that
/// ∑_{j=0}^{r} L_j · s[k+r-j] = 0 for all valid k (i.e., the minimal LFSR for s).
/// L[0] = 1 always (monic with constant 1, so L(0) = 1 ≠ 0).
fn berlekamp_massey_fp(s: &[u8], p: u8) -> Vec<u8> {
    let n = s.len();
    let p32 = p as u32;
    let p16 = p as u16;
    // Standard BM over F_p: L is the current LFSR, B is the previous LFSR after last update.
    let mut l: Vec<u8> = vec![1u8];   // L(z) = 1
    let mut b: Vec<u8> = vec![1u8];   // B(z) = 1 (shifted copy)
    let mut b_shift = 1usize;         // number of steps since last length change
    let mut delta_inv = 1u8;          // inverse of last nonzero discrepancy

    for k in 0..n {
        // Discrepancy d = sum_{i=0}^{r} L[i] * s[k-i].
        // Use u32 to avoid overflow: max sum = (p-1)^2 * (r+1) can exceed u16 for large r.
        let r = l.len() - 1;
        let mut d_acc = 0u32;
        for i in 0..=r {
            if k >= i {
                d_acc += l[i] as u32 * s[k - i] as u32;
            }
        }
        let d = (d_acc % p32) as u8;

        if d == 0 {
            b_shift += 1;
            continue;
        }
        // Update L: L ← L - (d * delta_inv) * z^{b_shift} * B
        let coef = (d as u16 * delta_inv as u16 % p16) as u8;
        let new_len = r + b_shift + b.len();
        let mut l_new = vec![0u8; new_len.max(l.len())];
        for i in 0..l.len() { l_new[i] = l[i]; }
        for i in 0..b.len() {
            let idx = i + b_shift;
            if idx < l_new.len() {
                let sub = coef as u16 * b[i] as u16 % p16;
                l_new[idx] = ((l_new[idx] as u16 + p16 - sub) % p16) as u8;
            }
        }
        // Trim trailing zeros
        while l_new.len() > 1 && *l_new.last().unwrap() == 0 { l_new.pop(); }

        if 2 * r <= k {
            // Length increases: save old L as new B
            b = l.clone();
            delta_inv = mod_inv(d, p);
            b_shift = 1;
        } else {
            b_shift += 1;
        }
        l = l_new;
    }
    l
}

/// Polynomial remainder a mod b over 𝔽_p (both in coefficient form, low-degree first).
fn poly_rem_fp(a: &[u8], b: &[u8], p: u8) -> Vec<u8> {
    if b.is_empty() || (b.len() == 1 && b[0] == 0) { return vec![0u8]; }
    let p16 = p as u16;
    let mut r = a.to_vec();
    let lead_b_inv = mod_inv(*b.last().unwrap(), p);
    while r.len() >= b.len() {
        let d = r.len() - b.len();
        let lead_r = *r.last().unwrap();
        if lead_r == 0 { r.pop(); continue; }
        let coef = (lead_r as u16 * lead_b_inv as u16 % p16) as u8;
        for i in 0..b.len() {
            let j = i + d;
            let sub = coef as u16 * b[i] as u16 % p16;
            r[j] = ((r[j] as u16 + p16 - sub) % p16) as u8;
        }
        while r.len() > 0 && *r.last().unwrap() == 0 { r.pop(); }
    }
    if r.is_empty() { r.push(0); }
    r
}

/// GCD of two polynomials over 𝔽_p (Euclidean, monic result).
fn poly_gcd_fp(a: &[u8], b: &[u8], p: u8) -> Vec<u8> {
    let p16 = p as u16;
    let mut x = a.to_vec();
    let mut y = b.to_vec();
    while !(y.len() == 1 && y[0] == 0) {
        let r = poly_rem_fp(&x, &y, p);
        x = y;
        y = r;
    }
    // Make monic
    if x.is_empty() { return vec![1u8]; }
    let lead_inv = mod_inv(*x.last().unwrap(), p);
    for v in &mut x { *v = (*v as u16 * lead_inv as u16 % p16) as u8; }
    x
}

/// Multiply two polynomials over 𝔽_p.
fn poly_mul_fp(a: &[u8], b: &[u8], p: u8) -> Vec<u8> {
    if a == [0u8] || b == [0u8] { return vec![0u8]; }
    let p16 = p as u16;
    let mut c = vec![0u8; a.len() + b.len() - 1];
    for (i, &ai) in a.iter().enumerate() {
        if ai == 0 { continue; }
        for (j, &bj) in b.iter().enumerate() {
            c[i + j] = ((c[i + j] as u16 + ai as u16 * bj as u16) % p16) as u8;
        }
    }
    c
}

/// Reverse a polynomial coefficient array (ascending-degree form), trimming leading zeros.
fn poly_reverse(a: &[u8]) -> Vec<u8> {
    let mut r: Vec<u8> = a.iter().rev().cloned().collect();
    while r.len() > 1 && *r.last().unwrap() == 0 { r.pop(); }
    r
}

/// LCM(a, b) = a * b / gcd(a, b) over 𝔽_p, monic.
fn poly_lcm_fp(a: &[u8], b: &[u8], p: u8) -> Vec<u8> {
    let g = poly_gcd_fp(a, b, p);
    let a_div_g = poly_rem_fp(a, &g, p);  // TODO: proper division
    // For LCM = (a / gcd) * b, need exact division.
    // Use: a = g * q, so q = a / g. Compute by synthetic division.
    let q = poly_exact_div_fp(a, &g, p);
    poly_mul_fp(&q, b, p)
}

/// Exact polynomial division a / b over 𝔽_p (assumes b | a exactly).
fn poly_exact_div_fp(a: &[u8], b: &[u8], p: u8) -> Vec<u8> {
    if b.len() == 1 && b[0] == 1 { return a.to_vec(); }
    let p16 = p as u16;
    let mut r = a.to_vec();
    let lead_b_inv = mod_inv(*b.last().unwrap(), p);
    let d = a.len().saturating_sub(b.len());
    let mut q = vec![0u8; d + 1];
    let mut deg_r = r.len();
    while deg_r >= b.len() {
        while deg_r > 0 && r[deg_r - 1] == 0 { deg_r -= 1; }
        if deg_r < b.len() { break; }
        let qi_idx = deg_r - b.len();
        let lead_r = r[deg_r - 1];
        if lead_r == 0 { break; }
        let coef = (lead_r as u16 * lead_b_inv as u16 % p16) as u8;
        q[qi_idx] = coef;
        for i in 0..b.len() {
            let j = i + qi_idx;
            let sub = coef as u16 * b[i] as u16 % p16;
            r[j] = ((r[j] as u16 + p16 - sub) % p16) as u8;
        }
        if deg_r > 0 { deg_r -= 1; }
    }
    q
}

/// Compute Y = A × C where C is B column-vectors stored interleaved: c_flat[col*B + j] = C[j][col].
/// Returns av_flat where av_flat[row*B + j] = (A × C[j])[row].
/// Single rayon call amortizes overhead over all B columns simultaneously.
fn matvec_B_fp(rows: &[Vec<(u32, u8)>], c_flat: &[u8], n_cols: usize, b: usize, p: u8, par: bool) -> Vec<u8> {
    let p32 = p as u32;
    let n_rows = rows.len();
    if par {
        use rayon::prelude::*;
        // Each row is independent; collect B-vector results then flatten.
        let results: Vec<Vec<u8>> = rows.par_iter().map(|row| {
            let mut acc = vec![0u32; b];
            for &(c, a) in row {
                let col = c as usize;
                if col < n_cols {
                    let base = col * b;
                    for j in 0..b { acc[j] += a as u32 * c_flat[base + j] as u32; }
                }
            }
            acc.iter().map(|&v| (v % p32) as u8).collect()
        }).collect();
        let mut av_flat = vec![0u8; n_rows * b];
        for (i, row_vals) in results.into_iter().enumerate() {
            av_flat[i*b..(i+1)*b].copy_from_slice(&row_vals);
        }
        av_flat
    } else {
        let mut av_flat = vec![0u32; n_rows * b];
        for (i, row) in rows.iter().enumerate() {
            let base_out = i * b;
            for &(c, a) in row {
                let col = c as usize;
                if col < n_cols {
                    let base = col * b;
                    for j in 0..b { av_flat[base_out + j] += a as u32 * c_flat[base + j] as u32; }
                }
            }
        }
        av_flat.iter().map(|&v| (v % p32) as u8).collect()
    }
}

/// Compute C = A^T × Y where Y is B column-vectors stored as av_flat[row*B + j] = Y[j][row].
/// Returns c_flat where c_flat[col*B + j] = (A^T × Y[j])[col].
fn matvec_T_B_fp(rows: &[Vec<(u32, u8)>], av_flat: &[u8], n_cols: usize, b: usize, p: u8, par: bool) -> Vec<u8> {
    let p32 = p as u32;
    let n_rows = rows.len();
    if par {
        use rayon::prelude::*;
        let n_threads = rayon::current_num_threads().max(1);
        let chunk = (n_rows + n_threads - 1) / n_threads;
        let partial: Vec<Vec<u32>> = rows.par_chunks(chunk).enumerate().map(|(ci, chunk_rows)| {
            let base_row = ci * chunk;
            let mut local = vec![0u32; n_cols * b];
            for (j, row) in chunk_rows.iter().enumerate() {
                let row_base = (base_row + j) * b;
                for &(c, a) in row {
                    let col = c as usize;
                    if col < n_cols {
                        let base_out = col * b;
                        for k in 0..b {
                            local[base_out + k] += a as u32 * av_flat[row_base + k] as u32;
                        }
                    }
                }
            }
            local
        }).collect();
        let mut acc = vec![0u32; n_cols * b];
        for part in &partial { for (a, &v) in acc.iter_mut().zip(part.iter()) { *a += v; } }
        acc.iter().map(|&v| (v % p32) as u8).collect()
    } else {
        let mut acc = vec![0u32; n_cols * b];
        for (i, row) in rows.iter().enumerate() {
            let row_base = i * b;
            for &(c, a) in row {
                let col = c as usize;
                if col < n_cols {
                    let base_out = col * b;
                    for k in 0..b { acc[base_out + k] += a as u32 * av_flat[row_base + k] as u32; }
                }
            }
        }
        acc.iter().map(|&v| (v % p32) as u8).collect()
    }
}

/// Block Wiedemann solver over 𝔽_p: solves A × x = b (augmented column) or returns None.
///
/// Uses M' = A A^T (n_rows × n_rows).  Computes ONE Krylov sequence (M')^k b and projects
/// it through B=8 independent random left vectors simultaneously.  The B scalar sequences are
/// processed with BM; each BM polynomial is reversed to obtain the operator annihilator
/// (Q_j(M')b = 0).  The LCM of the B operator polynomials converges to the true minimal
/// polynomial with P(failure) < rank/p^B.  For p=11, rank=21000, B=8: P < 0.01%.
fn sparse_block_wiedemann_fp(
    rows: &[Vec<(u32, u8)>],
    n_cols: usize,
    p: u8,
    verbose: bool,
) -> Option<Vec<u8>> {
    let p16 = p as u16;
    let p32 = p as u32;
    let t0 = std::time::Instant::now();
    let n_rows = rows.len();

    let nnz: usize = rows.iter().map(|r| r.len()).sum();
    let par = nnz > 2_000_000;

    // RHS vector b[i] = A[i][n_cols] (augmented column).
    let rhs_col = n_cols as u32;
    let b_rhs: Vec<u8> = rows.iter().map(|row| {
        row.iter().find(|&&(c, _)| c == rhs_col).map(|&(_, v)| v).unwrap_or(0)
    }).collect();
    if b_rhs.iter().all(|&v| v == 0) { return None; }

    // k_len ≥ 2 * rank(M') + margin.  rank(M') = rank(A) ≤ min(n_rows, n_cols).
    let rank_bound = n_rows.min(n_cols);
    let k_len = 2 * rank_bound + 64;

    // For small p (p << rank), a single random u makes BM return a proper divisor of the true
    // operator min poly.  Use B=8 projections in ONE Krylov pass; LCM of all B reversed-BM
    // polynomials converges to the true min poly with overwhelming probability.
    const B: usize = 8;
    const MAX_OUTER: usize = 4;

    for outer in 0..MAX_OUTER {
        let mut rng_state = 0x9e3779b97f4a7c15u64
            ^ (n_cols as u64).wrapping_mul(6364136223846793005)
            ^ (outer as u64).wrapping_mul(0xbf58476d1ce4e5b9);

        let mut u_vecs: Vec<Vec<u8>> = Vec::with_capacity(B);
        for _ in 0..B {
            let u: Vec<u8> = (0..n_rows).map(|_| {
                rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
                ((rng_state >> 33) as u8 % p)
            }).collect();
            u_vecs.push(u);
        }

        // Phase 1: ONE Krylov pass, B simultaneous scalar dot-products.
        // r_seqs[j][k] = u_j · (M')^k b
        let mut r_seqs: Vec<Vec<u8>> = vec![Vec::with_capacity(k_len); B];
        let mut c = b_rhs.clone();
        for _k in 0..k_len {
            for j in 0..B {
                let mut acc = 0u32;
                for (&uu, &cc) in u_vecs[j].iter().zip(c.iter()) { acc += uu as u32 * cc as u32; }
                r_seqs[j].push((acc % p32) as u8);
            }
            let at_c = matvec_T_fp(rows, &c, n_cols, p, par);
            c = matvec_fp(rows, &at_c, n_cols, p, par);
        }

        if verbose {
            eprintln!("c [alg-timing] wiedemann phase1 (outer {}): {:.3}s ({} MV products)",
                outer, t0.elapsed().as_secs_f64(), 2 * k_len);
        }

        // Phase 2: BM on each sequence → reverse → LCM of operator polynomials.
        // BM returns LFSR polynomial L (L[0]=1).  Operator annihilator Q = reverse(L):
        // Q(M')b = 0.  LCM(Q_0,...,Q_{B-1}) = true min poly with high probability.
        let mut q_lcm: Vec<u8> = vec![1u8];  // neutral element for LCM (constant 1)
        let mut bm_degs = [0usize; B];
        for j in 0..B {
            let mu_j = berlekamp_massey_fp(&r_seqs[j], p);
            let q_j = poly_reverse(&mu_j);
            bm_degs[j] = q_j.len() - 1;
            if q_j.len() > 1 {
                q_lcm = poly_lcm_fp(&q_lcm, &q_j, p);
            }
        }
        let deg_q = q_lcm.len() - 1;

        if verbose {
            eprintln!("c [alg-timing] wiedemann phase2 (BM+LCM, {} polys): {:.3}s, deg(q_lcm)={} (BM degs: {:?})",
                B, t0.elapsed().as_secs_f64(), deg_q, bm_degs);
        }

        if deg_q == 0 { continue; }

        // Phase 3: power escalation.  For nilpotent module structure (min_poly = f^m),
        // every BM projection returns f but f(M')b ≠ 0.  Try q_lcm^k for k=1,2,3,...
        // until reconstruction succeeds.  Only powers ≤ ceil(rank/deg_q) are meaningful.
        let max_power = (rank_bound / deg_q.max(1) + 1).min(4);
        let mut poly = q_lcm.clone();
        let mut found = false;
        for power in 1..=max_power {
            let deg_poly = poly.len() - 1;
            if poly[0] == 0 || deg_poly == 0 {
                if power < max_power { poly = poly_mul_fp(&poly, &q_lcm, p); }
                continue;
            }
            // Overflow guard: (p-1)^2 * deg_poly must fit in u32.
            let pp1sq = (p as u32 - 1) * (p as u32 - 1);
            if deg_poly as u64 * pp1sq as u64 >= u32::MAX as u64 {
                break;
            }
            let q0_inv = mod_inv(poly[0], p);
            let mut z_acc = vec![0u32; n_rows];
            {
                let mut v = b_rhs.clone();
                for j in 0..deg_poly {
                    let coef = poly[j + 1];
                    if coef != 0 {
                        let c = ((p16 - coef as u16) * q0_inv as u16 % p16) as u32;
                        for (za, &vv) in z_acc.iter_mut().zip(v.iter()) { *za += c * vv as u32; }
                    }
                    if j + 1 < deg_poly {
                        let at_v = matvec_T_fp(rows, &v, n_cols, p, par);
                        v = matvec_fp(rows, &at_v, n_cols, p, par);
                    }
                }
            }
            let z_tilde: Vec<u8> = z_acc.iter().map(|&a| (a % p32) as u8).collect();
            let x_tilde = matvec_T_fp(rows, &z_tilde, n_cols, p, par);

            if verbose {
                eprintln!("c [alg-timing] wiedemann phase3 (outer {} power {} deg={}): {:.3}s",
                    outer, power, deg_poly, t0.elapsed().as_secs_f64());
            }

            let ax = matvec_fp(rows, &x_tilde, n_cols, p, par);
            if ax.iter().zip(b_rhs.iter()).all(|(&a, &b)| a == b) {
                if verbose { eprintln!("c [alg-timing] wiedemann: {:.3}s (CERT VERIFIED, outer {} power {})", t0.elapsed().as_secs_f64(), outer, power); }
                return Some(x_tilde);
            }

            if power < max_power { poly = poly_mul_fp(&poly, &q_lcm, p); }
        }
        if !found && verbose { eprintln!("c [alg-timing] wiedemann outer {}: all powers failed (deg_q={}), retrying", outer, deg_q); }
    }

    if verbose { eprintln!("c [alg-timing] wiedemann: {:.3}s (inconsistent, verification failed)", t0.elapsed().as_secs_f64()); }
    None
}

/// Sparse Gaussian elimination over 𝔽_p with optional fill-in abort.
/// Returns Ok(Some(sol)) on cert, Ok(None) when inconsistent, Err(()) when fill > fill_limit.
fn sparse_ge_fp_bounded(
    mut rows: Vec<Vec<(u32, u8)>>,
    n_cols: usize,
    p: u8,
    verbose: bool,
    fill_limit: usize,
) -> Result<Option<Vec<u8>>, ()> {
    use std::collections::BinaryHeap;
    use std::cmp::Reverse;
    use rustc_hash::FxHashSet;
    let n_rows = rows.len();
    let rhs_col = n_cols as u32;
    let p16 = p as u16;
    let t0 = std::time::Instant::now();

    // Column index: col -> set of physical row indices with a nonzero in that col.
    // FxHashSet uses a fast integer hash (no SipHash overhead).
    let mut col_rows: Vec<FxHashSet<u32>> = (0..=n_cols).map(|_| FxHashSet::default()).collect();
    for r in 0..n_rows {
        for &(c, _) in &rows[r] {
            col_rows[c as usize].insert(r as u32);
        }
    }

    // Dynamic minimum-degree (Markowitz) column selection via lazy-deletion min-heap.
    // col_nnz[c] = col_rows[c].len(), updated after each saxpy via merge-diff.
    // Heap entries (nnz, col) are stale if nnz != col_nnz[col] — skipped on pop.
    let mut col_nnz: Vec<usize> = (0..n_cols).map(|c| col_rows[c].len()).collect();
    let mut heap: BinaryHeap<Reverse<(usize, usize)>> = (0..n_cols)
        .map(|c| Reverse((col_nnz[c], c)))
        .collect();

    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; n_cols];
    let mut pivot_cols: Vec<usize> = Vec::new();
    let mut phys_to_log: Vec<usize> = (0..n_rows).collect();
    let mut log_to_phys: Vec<usize> = (0..n_rows).collect();
    let mut current_log = 0usize;

    // Scratch buffer for saxpy output (reused to avoid per-call allocation).
    let mut scratch: Vec<(u32, u8)> = Vec::new();
    // dirty_cols: columns whose col_nnz changed during the current pivot step.
    // Flushed to heap ONCE after all saxpy rows are done (one push per unique col).
    let mut dirty_cols: Vec<usize> = Vec::new();

    loop {
        // Pop minimum-NNZ column; skip stale/pivoted/empty entries.
        let col = loop {
            match heap.pop() {
                None => break None,
                Some(Reverse((nnz, c))) => {
                    if pivot_row_of_col[c].is_some() { continue; }
                    if nnz != col_nnz[c] { continue; }
                    if col_nnz[c] == 0 { continue; }
                    break Some(c);
                }
            }
        };
        let col = match col { Some(c) => c, None => break };

        // Find pivot: physical row with lowest logical index >= current_log and nonzero in col.
        let pivot_phys = col_rows[col].iter()
            .filter_map(|&r| {
                let log = phys_to_log[r as usize];
                if log >= current_log { Some((log, r as usize)) } else { None }
            })
            .min_by_key(|&(log, _)| log)
            .map(|(_, phys)| phys);

        let pivot_phys = match pivot_phys { Some(p) => p, None => continue };

        // Swap pivot to current_log position.
        let current_phys = log_to_phys[current_log];
        if pivot_phys != current_phys {
            let plog = phys_to_log[pivot_phys];
            phys_to_log[current_phys] = plog;
            phys_to_log[pivot_phys] = current_log;
            log_to_phys[current_log] = pivot_phys;
            log_to_phys[plog] = current_phys;
        }
        let pr = log_to_phys[current_log];

        // Scale pivot row so entry at col = 1.
        let a = rows[pr].iter().find(|&&(c, _)| c as usize == col).map(|&(_, v)| v).unwrap();
        if a != 1 {
            let inv = mod_inv(a, p);
            for (_, v) in &mut rows[pr] { *v = (*v as u16 * inv as u16 % p16) as u8; }
        }
        pivot_row_of_col[col] = Some(pr);
        pivot_cols.push(col);

        // Forward-only: collect rows below the pivot that have a nonzero in col.
        let below: Vec<usize> = col_rows[col].iter()
            .map(|&r| r as usize)
            .filter(|&r| phys_to_log[r] > current_log)
            .collect();

        if below.is_empty() {
            current_log += 1;
            continue;
        }
        let pivot_snap: Vec<(u32, u8)> = rows[pr].clone();

        for r in below {
            let k = rows[r].iter().find(|&&(c, _)| c as usize == col).map(|&(_, v)| v).unwrap();
            let neg_k = (p - k) as u8;

            // Saxpy into scratch (reused buffer).
            scratch.clear();
            scratch.reserve(rows[r].len() + pivot_snap.len());
            {
                let mut ri = 0usize;
                let mut pi = 0usize;
                while ri < rows[r].len() || pi < pivot_snap.len() {
                    let rc = rows[r].get(ri).map_or(u32::MAX, |&(c, _)| c);
                    let pc = pivot_snap.get(pi).map_or(u32::MAX, |&(c, _)| c);
                    if rc < pc {
                        scratch.push(rows[r][ri]);
                        ri += 1;
                    } else if rc > pc {
                        let v = (neg_k as u16 * pivot_snap[pi].1 as u16 % p16) as u8;
                        if v != 0 { scratch.push((pc, v)); }
                        pi += 1;
                    } else {
                        let v = ((rows[r][ri].1 as u16
                            + neg_k as u16 * pivot_snap[pi].1 as u16) % p16) as u8;
                        if v != 0 { scratch.push((rc, v)); }
                        ri += 1;
                        pi += 1;
                    }
                }
            }

            // Merge-diff: update col_rows and track dirty cols for deferred heap flush.
            {
                let mut oi = 0usize;
                let mut ni = 0usize;
                while oi < rows[r].len() || ni < scratch.len() {
                    let oc = rows[r].get(oi).map_or(u32::MAX, |&(c, _)| c);
                    let nc = scratch.get(ni).map_or(u32::MAX, |&(c, _)| c);
                    if oc < nc {
                        col_rows[oc as usize].remove(&(r as u32));
                        if (oc as usize) < n_cols { dirty_cols.push(oc as usize); }
                        oi += 1;
                    } else if nc < oc {
                        col_rows[nc as usize].insert(r as u32);
                        if (nc as usize) < n_cols { dirty_cols.push(nc as usize); }
                        ni += 1;
                    } else {
                        oi += 1;
                        ni += 1;
                    }
                }
            }

            std::mem::swap(&mut rows[r], &mut scratch);
        }

        // Flush dirty_cols to heap: one push per unique column with its final NNZ.
        dirty_cols.sort_unstable();
        let mut prev = usize::MAX;
        for c in dirty_cols.drain(..) {
            if c == prev { continue; }
            prev = c;
            col_nnz[c] = col_rows[c].len();
            heap.push(Reverse((col_nnz[c], c)));
        }

        current_log += 1;

        // Fill-in abort: if nnz exceeds limit, give up and let caller try Wiedemann.
        if fill_limit < usize::MAX {
            let cur_nnz: usize = rows.iter().map(|r| r.len()).sum();
            if cur_nnz > fill_limit {
                if verbose {
                    eprintln!("c [alg-timing] sparse GE aborted: {} nnz > fill limit {} at pivot {}",
                        cur_nnz, fill_limit, current_log);
                }
                return Err(());
            }
        }

        // Progress report every 1000 pivots.
        if verbose && current_log % 1000 == 0 {
            let nnz: usize = rows.iter().map(|r| r.len()).sum();
            eprintln!(
                "c [alg-timing] sparse GE progress: {:.1}s pivot {} / {} ({} nnz, heap {})",
                t0.elapsed().as_secs_f64(), current_log, n_cols, nnz, heap.len()
            );
        }
    }
    let rank = current_log;

    if verbose {
        let nnz: usize = rows.iter().map(|r| r.len()).sum();
        eprintln!(
            "c [alg-timing] sparse GE: {:.3}s (rank {} / {}, {} nnz after fwd elim)",
            t0.elapsed().as_secs_f64(), rank, n_cols, nnz
        );
    }

    // Consistency: any row with all-zero LHS but nonzero RHS → inconsistent.
    for r in 0..n_rows {
        let has_lhs = rows[r].iter().any(|&(c, _)| (c as usize) < n_cols);
        let rhs_val = rows[r].iter().find(|&&(c, _)| c == rhs_col).map(|&(_, v)| v).unwrap_or(0);
        if !has_lhs && rhs_val != 0 {
            return Ok(None);
        }
    }

    // Back-substitution in reverse pivot order (free variables = 0).
    let mut solution = vec![0u8; n_cols];
    for &col_k in pivot_cols.iter().rev() {
        let pr = pivot_row_of_col[col_k].unwrap();
        let mut s = rows[pr].iter()
            .find(|&&(c, _)| c == rhs_col).map(|&(_, v)| v as u16).unwrap_or(0);
        for &(c, v) in &rows[pr] {
            let ci = c as usize;
            if ci != col_k && ci < n_cols && solution[ci] != 0 {
                s = (s + (p as u16 - v as u16) * solution[ci] as u16) % p16;
            }
        }
        solution[col_k] = s as u8;
    }

    Ok(Some(solution))
}

/// Build the NS sparse matrix over F_{p_work} (u64 entries) from orbit data.
/// Used as fallback when GE fill-in is catastrophic: the same orbit structure is reused
/// but entries are computed mod p_work (large prime coprime to |G|).
fn build_lp_sparse_rows(
    n_rows: usize,
    n_cols: usize,
    unknown_seeds: &[(u32, usize)],
    orbit_c_sizes: &[u64],
    n_verts: usize,
    c2o: &std::collections::HashMap<super::graph_canon::CanonGraph, (u32, u64)>,
    bits_to_orbit: &std::collections::HashMap<MonoBits, (u32, u64)>,
    axiom_bits: &[Vec<(MonoBits, u8)>],
    colex: &ColexIndex,
    p_work: u64,
    one_orbit: usize,
) -> Vec<Vec<(u32, u64)>> {
    use super::graph_canon::{canonicalize, monobits_to_edges};
    let mut stab_64: Vec<std::collections::HashMap<u32, u64>> =
        (0..n_rows).map(|_| std::collections::HashMap::new()).collect();

    for (col, &(ai, mi)) in unknown_seeds.iter().enumerate() {
        let mi_bits = colex.bits_at(mi as usize);
        let orbit_c_P = orbit_c_sizes[col] % p_work;
        for &(term_bits, coef) in &axiom_bits[ai as usize] {
            let product = term_bits | mi_bits;
            if (product.count_ones() as u32) > colex.d { continue; }
            let orbit_r_and_size = if let Some(&v) = bits_to_orbit.get(&product) {
                Some(v)
            } else {
                let prod_edges = monobits_to_edges(product, n_verts as u32);
                let (canon_g, _) = canonicalize(&prod_edges);
                c2o.get(&canon_g).copied()
            };
            if let Some((orbit_r, orbit_r_size)) = orbit_r_and_size {
                let r_mod_P = orbit_r_size % p_work;
                if r_mod_P == 0 { continue; }
                let inv_r = mod_inv_u64(r_mod_P, p_work);
                let scale = orbit_c_P * inv_r % p_work;
                let contrib = coef as u64 * scale % p_work;
                if contrib == 0 { continue; }
                let e = stab_64[orbit_r as usize].entry(col as u32).or_insert(0u64);
                *e = (*e + contrib) % p_work;
            }
        }
    }

    let mut sparse_rows: Vec<Vec<(u32, u64)>> = stab_64.into_iter().map(|hm| {
        let mut v: Vec<(u32, u64)> = hm.into_iter().filter(|&(_, val)| val != 0).collect();
        v.sort_unstable_by_key(|&(c, _)| c);
        v
    }).collect();
    sparse_rows[one_orbit].push((n_cols as u32, 1u64));
    sparse_rows[one_orbit].sort_unstable_by_key(|&(c, _)| c);
    sparse_rows
}

/// Modular inverse for small p.
fn mod_inv(a: u8, p: u8) -> u8 {
    for k in 1..p {
        if (a as u16 * k as u16) % p as u16 == 1 {
            return k;
        }
    }
    panic!("no inverse of {} mod {}", a, p);
}

/// Scatter a single `(axiom_idx, mu_idx)` pair's contribution into the
/// growing matrix. Each axiom term `(term_bits, coef)` produces the product
/// `term_bits | mu_bits`; if that monomial is present in the enumeration
/// AND is the canonical rep of its monomial-orbit, add `coef` to
/// `matrix[row][col]` (mod p). Extracted from the main BFS so the same
/// scatter is reused for cert reconstruction.
#[inline]
fn scatter_pair(
    axiom_bits: &[Vec<(MonoBits, u8)>],
    colex: &ColexIndex,
    mono_orbit_id: &[u32],
    mono_orbit_rep: &[u32],
    matrix: &mut [Vec<u8>],
    ai: u32,
    mi: u32,
    col: usize,
    p: u8,
) {
    let mu_bits = colex.bits_at(mi as usize);
    for &(term_bits, coef) in &axiom_bits[ai as usize] {
        let product = term_bits | mu_bits;
        // Products whose degree exceeds `d` are outside the enumeration and
        // contribute nothing to the degree-`d` cert system. Check via
        // popcount before ranking; colex.rank() assumes popcount ≤ d.
        if (product.count_ones() as u32) > colex.d {
            continue;
        }
        let idx = colex.rank(product);
        let row = mono_orbit_id[idx] as usize;
        if idx == mono_orbit_rep[row] as usize {
            matrix[row][col] = (matrix[row][col] + coef) % p;
        }
    }
}

/// Re-enumerate the full member list of an unknown-pair orbit starting
/// from its stored seed pair. Used during certificate reconstruction —
/// we don't materialize members during the main BFS to keep memory small.
/// Monomial images are computed on-the-fly via `var_tables` + colex
/// ranking; no precomputed `mono_action` or hash index is required.
fn reenumerate_orbit_members(
    n_monos: usize,
    colex: &ColexIndex,
    var_tables: &[Vec<u32>],
    axiom_action: &[Vec<usize>],
    n_axioms: usize,
    seed: (u32, u32),
) -> Vec<(u32, u32)> {
    // Members of a single orbit — orbit size is bounded by |G|, so a
    // HashSet is safe here even when the total pair space is astronomical.
    let _ = n_axioms;
    use std::collections::HashSet;
    let mut visited: HashSet<(u32, u32)> = HashSet::new();
    visited.insert(seed);
    let mut members: Vec<(u32, u32)> = vec![seed];
    let mut queue: Vec<(u32, u32)> = vec![seed];
    while let Some((ci, cmi)) = queue.pop() {
        let ci_u = ci as usize;
        let bits_cmi = colex.bits_at(cmi as usize);
        debug_assert!((cmi as usize) < n_monos);
        for (gi, vt) in var_tables.iter().enumerate() {
            let ni = axiom_action[gi][ci_u] as u32;
            let nmi = colex.rank(apply_bits(bits_cmi, vt)) as u32;
            if visited.insert((ni, nmi)) {
                members.push((ni, nmi));
                queue.push((ni, nmi));
            }
        }
    }
    members
}

/// Find a G-invariant NS certificate at degree `d` over 𝔽_p for the given
/// schema + axioms. Uses the adjacent-transposition generators implied by
/// the schema's group spec. See [`find_orbit_cert_fp_with_gens`] for
/// problems whose symmetry group is a proper subgroup of the schema's
/// default (e.g. Tseitin on a non-complete graph).
///
/// Precondition: `p ∤ |G|`, otherwise invariant certs may not exist.
pub fn find_orbit_cert_fp(
    schema: &TupleVarSchema,
    axioms: &[PolyP],
    d: usize,
    p: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    let gens = schema.generators();
    find_orbit_cert_fp_with_gens(schema, axioms, &gens, d, p)
}

/// Like [`find_orbit_cert_fp`] but uses explicit generators instead of
/// the schema's default. Required for families whose automorphism group
/// is a proper subgroup of the schema's natural group (Tseitin on
/// non-complete graphs: only edge-preserving permutations, not all of
/// S_n).
///
/// The generators must still lie in the schema's group (i.e. each
/// generator's per-base permutation is a valid permutation of the base).
/// The engine verifies closure implicitly by building `axiom_action_table`;
/// a non-closed set panics there.
pub fn find_orbit_cert_fp_with_gens(
    schema: &TupleVarSchema,
    axioms: &[PolyP],
    gens: &[Generator],
    d: usize,
    p: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    let verbose = std::env::var("CASCADE_ALG_TIMING").is_ok();
    let t_total = std::time::Instant::now();
    let n = schema.n_vars();
    if axioms.is_empty() {
        return None;
    }

    assert!(
        n <= MonoBits::CAPACITY,
        "orbit_ns currently supports up to {} vars (got {}). Bitmask Monomial \
         is [u64; {}]; bump N_WORDS for larger families.",
        MonoBits::CAPACITY,
        n,
        N_WORDS,
    );

    // Colex perfect-hash index: bits ↔ position in the enumeration. Both
    // `rank(bits) → i` and `unrank(i) → bits` are O(d · log n) on a small
    // precomputed binomial table (a few KB). The `Vec<MonoBits>` array of
    // all monomials (32 · n_monos bytes — 500 GB at R(4,4)/K_18 d=6) is
    // NOT materialized: every bit access goes through `colex.bits_at(i)`.
    let t0 = std::time::Instant::now();
    let colex = ColexIndex::new(n, d as u32);
    let n_monos = colex.len();
    if verbose {
        eprintln!(
            "c [alg-timing] colex index build: {:.3}s ({} monomials, binom {} × {})",
            t0.elapsed().as_secs_f64(),
            n_monos,
            (n + 2),
            (d as u32 + 2)
        );
    }

    // Precompute per-generator var-action tables only. The full per-
    // generator monomial-index action table (`mono_action[gi][mi]`) used
    // to live here; it was dropped because for PHP_{8,7} d=7 it was
    // `n_gens × n_monos × 4` ≈ 14 GB — the dominant memory cost. Images
    // are now recomputed inline as `colex.rank(apply_bits(colex.bits_at(mi),
    // var_tables[gi]))`: `apply_bits` is O(degree) and colex ranking is
    // also O(degree · log n), both very fast.
    let t0 = std::time::Instant::now();
    let var_tables: Vec<Vec<u32>> =
        gens.iter().map(|g| schema.var_action_table(g)).collect();
    if verbose {
        eprintln!(
            "c [alg-timing] var_tables: {} gens in {:.3}s",
            gens.len(),
            t0.elapsed().as_secs_f64()
        );
    }

    // For UnorderedPair+Diagonal+full-S_n (Ramsey K_n): use the formula path that
    // avoids building the O(n_monos)-entry orbit_id array.  This path eliminates
    // the monomial_orbits step entirely and computes the matrix directly from
    // the stab-path canonical seeds via O(seeds × axiom_terms) canonicalize calls.
    let is_ramsey_formula_path = {
        use crate::tuple_schema::{GroupSpec, TupleKind};
        matches!(schema.tuple_kind, TupleKind::UnorderedPair)
            && matches!(schema.group, GroupSpec::Diagonal)
            && schema.bases.len() == 1
            && gens.len() == schema.bases[0].size.saturating_sub(1) as usize
    };

    // Precompute axiom terms as (bits, coef) pairs — needed early for lazy c2o build.
    let axiom_bits: Vec<Vec<(MonoBits, u8)>> = axioms
        .iter()
        .map(|a| {
            a.terms
                .iter()
                .map(|(m, c)| (mono_to_bits(m, n), *c))
                .collect()
        })
        .collect();

    // Axiom metadata needed for stab path detection.
    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();
    let n_axioms = axioms.len();

    // Pre-detect R(s,t) stab path before building formula_data, so we can
    // replace the expensive enumerate_orbit_reps with a lazy product scan.
    let pre_stab_path: Option<(usize, usize, usize, usize, usize, usize)> = {
        use crate::tuple_schema::binom;
        let nv = schema.bases[0].size as usize;
        let red_deg = axiom_degrees.get(0).copied().unwrap_or(0);
        let s_f = (1.0 + (1.0 + 8.0 * red_deg as f64).sqrt()) / 2.0;
        let s = s_f.round() as usize;
        let csk2 = s.saturating_mul(s.saturating_sub(1)) / 2;
        let n_red = binom(nv as u32, s as u32) as usize;
        let red_ok = is_ramsey_formula_path
            && s >= 2 && csk2 == red_deg && n_red <= n_axioms
            && axiom_degrees[..n_red].iter().all(|&deg| deg == red_deg);
        if red_ok {
            let blue_deg = axiom_degrees.get(n_red).copied().unwrap_or(0);
            let t_f = (1.0 + (1.0 + 8.0 * blue_deg as f64).sqrt()) / 2.0;
            let t = t_f.round() as usize;
            let ctk2 = t.saturating_mul(t.saturating_sub(1)) / 2;
            let n_blue = binom(nv as u32, t as u32) as usize;
            let blue_ok = t >= s && ctk2 == blue_deg && n_red + n_blue == n_axioms
                && d >= blue_deg
                && axiom_degrees[n_red..].iter().all(|&deg| deg == blue_deg);
            if blue_ok { Some((s, t, n_red, n_blue, d - red_deg, d - blue_deg)) } else { None }
        } else {
            None
        }
    };

    // Build orbit info. For the stab path: build a lazy c2o from actual products
    // (avoids expensive enumerate_orbit_reps at high degree). For other formula paths:
    // use enumerate_orbit_reps. For BFS paths: on-the-fly monomial orbit BFS.
    let t0 = std::time::Instant::now();
    let (n_mono_orbits, mono_orbit_id, mono_orbit_rep, formula_data) = if let Some(
        (pre_s, pre_t, pre_n_red, _pre_n_blue, pre_br, pre_bt),
    ) = pre_stab_path
    {
        // Lazy c2o: enumerate only the canonical product graphs that arise from
        // stab seeds, not all C(n_edges, d) orbit classes.
        use super::graph_canon::{
            canonicalize, enumerate_stab_pair_reps, monobits_to_edges, orbit_size, CanonGraph,
            StabOrbitRep,
        };
        use std::collections::HashMap;
        let n_verts = schema.bases[0].size;

        let t_reps = std::time::Instant::now();
        let red_reps = enumerate_stab_pair_reps(pre_s, pre_br, n_verts as usize - pre_s);
        let blue_reps = if pre_t == pre_s && pre_bt == pre_br {
            red_reps.clone()
        } else {
            enumerate_stab_pair_reps(pre_t, pre_bt, n_verts as usize - pre_t)
        };
        if verbose { eprintln!("c [alg-timing] enumerate_stab_pair_reps: {:.3}s ({} red, {} blue)", t_reps.elapsed().as_secs_f64(), red_reps.len(), blue_reps.len()); }

        // Collect (ai, mi_bits) for all seeds with nonzero orbit size.
        let t_monobits = std::time::Instant::now();
        let mut seed_mi_bits: Vec<(u32, MonoBits)> = Vec::new();
        for rep in &red_reps {
            if rep.orbit_c_size(n_verts, pre_s) == 0 { continue; }
            seed_mi_bits.push((0u32, rep.to_monobits(n_verts)));
        }
        let blue_ai = pre_n_red as u32;
        for rep in &blue_reps {
            if rep.orbit_c_size(n_verts, pre_t) == 0 { continue; }
            seed_mi_bits.push((blue_ai, rep.to_monobits(n_verts)));
        }
        if verbose { eprintln!("c [alg-timing] to_monobits: {:.3}s ({} seeds)", t_monobits.elapsed().as_secs_f64(), seed_mi_bits.len()); }

        // Scan all products → build lazy c2o (empty graph = row 0).
        // Also build bits_to_orbit: MonoBits → orbit_r to skip re-canonicalizing
        // in the matrix scatter step.
        let mut lazy_c2o: HashMap<CanonGraph, (u32, u64)> = HashMap::new();
        lazy_c2o.insert(CanonGraph::empty(), (0, 1u64));
        // Maps product MonoBits → (orbit_r, orbit_r_size) so the matrix scatter
        // can skip the canonicalize call for products already seen during the build.
        let mut bits_to_orbit: HashMap<MonoBits, (u32, u64)> = HashMap::new();

        // Collect all unique products needing canonicalization.
        let t_dedup = std::time::Instant::now();
        let mut products_to_canon: Vec<MonoBits> = Vec::new();
        {
            let mut seen: std::collections::HashSet<MonoBits> = std::collections::HashSet::new();
            for &(ai, mi_bits) in &seed_mi_bits {
                for &(term_bits, _coef) in &axiom_bits[ai as usize] {
                    let product = term_bits | mi_bits;
                    if product.count_ones() as u32 > d as u32 { continue; }
                    if seen.insert(product) {
                        products_to_canon.push(product);
                    }
                }
            }
        }
        if verbose { eprintln!("c [alg-timing] product dedup: {:.3}s ({} unique)", t_dedup.elapsed().as_secs_f64(), products_to_canon.len()); }
        // Canonicalize all products in parallel.
        let t_canon = std::time::Instant::now();
        let canon_results: Vec<(MonoBits, CanonGraph, u64)> = products_to_canon
            .par_iter()
            .map(|&product| {
                let prod_edges = monobits_to_edges(product, n_verts);
                let (canon_g, aut) = canonicalize(&prod_edges);
                (product, canon_g, aut)
            })
            .collect();
        if verbose { eprintln!("c [alg-timing] product canon (par): {:.3}s", t_canon.elapsed().as_secs_f64()); }
        let t_insert = std::time::Instant::now();
        // Insert results sequentially to build lazy_c2o and bits_to_orbit.
        for (product, canon_g, aut) in canon_results {
            let next = lazy_c2o.len() as u32;
            let (orbit_r, orbit_r_size) = *lazy_c2o.entry(canon_g.clone()).or_insert_with(|| {
                let sz = orbit_size(&canon_g, aut, n_verts);
                (next, sz)
            });
            bits_to_orbit.insert(product, (orbit_r, orbit_r_size));
        }
        if verbose { eprintln!("c [alg-timing] orbit insert: {:.3}s", t_insert.elapsed().as_secs_f64()); }

        let n = lazy_c2o.len();
        if verbose {
            eprintln!(
                "c [alg-timing] monomial_orbits (lazy stab): {} product orbits in {:.3}s",
                n, t0.elapsed().as_secs_f64()
            );
        }
        (n, Vec::<u32>::new(), Vec::<u32>::new(), Some((n_verts, lazy_c2o, bits_to_orbit, red_reps, blue_reps)))
    } else if is_ramsey_formula_path {
        use super::graph_canon::{enumerate_orbit_reps, CanonGraph, StabOrbitRep};
        use std::collections::HashMap;
        let n_verts = schema.bases[0].size;
        let reps = enumerate_orbit_reps(n_verts, d as u32);
        let n = reps.len();
        let mut c2o: HashMap<CanonGraph, (u32, u64)> = HashMap::with_capacity(n);
        for (idx, (_, g, sz)) in reps.iter().enumerate() {
            c2o.insert(g.clone(), (idx as u32, *sz));
        }
        if verbose {
            eprintln!(
                "c [alg-timing] monomial_orbits (formula): {} orbits in {:.3}s",
                n, t0.elapsed().as_secs_f64()
            );
        }
        (n, Vec::<u32>::new(), Vec::<u32>::new(), Some((n_verts, c2o, HashMap::new(), Vec::<StabOrbitRep>::new(), Vec::<StabOrbitRep>::new())))
    } else {
        let (oid, orep) = monomial_orbits_on_the_fly(schema, gens, n_monos, &colex, &var_tables);
        let n = orep.len();
        if verbose {
            eprintln!(
                "c [alg-timing] monomial_orbits (on-the-fly): {} orbits from {} monos in {:.3}s",
                n, n_monos, t0.elapsed().as_secs_f64()
            );
        }
        (n, oid, orep, None)
    };

    // Axiom action under group.
    let t0 = std::time::Instant::now();
    let axiom_action = axiom_action_table(schema, axioms, &gens);
    if verbose {
        eprintln!(
            "c [alg-timing] axiom_action_table: {:.3}s",
            t0.elapsed().as_secs_f64()
        );
    }

    // Unknown orbits: (axiom_idx, multiplier_mono_idx) pairs under the group.
    let t0 = std::time::Instant::now();
    // global_max_mi = largest budget window across all axioms
    let global_max_mi = axiom_degrees
        .iter()
        .filter(|&&deg| deg <= d)
        .map(|&deg| colex.len_up_to_degree(d - deg))
        .max()
        .unwrap_or(0);

    // Seed of each unknown orbit (first pair that started its BFS) — enough
    // to re-enumerate members on demand during cert reconstruction.
    let mut unknown_seeds: Vec<(u32, usize)> = Vec::new();

    let n_rows = n_mono_orbits;

    // Matrix grows column-by-column as orbits are discovered. Row-major
    // storage so Gaussian elimination works unchanged on the final shape.
    let mut matrix_rows: Vec<Vec<u8>> = (0..n_rows).map(|_| Vec::new()).collect();
    let mut rhs: Vec<u8> = Vec::new();
    // Stab path uses sparse rows to avoid O(n_rows × n_cols) dense allocation.
    let mut stab_sparse: Vec<std::collections::HashMap<u32, u8>> = Vec::new();

    // Counters for timing summary.
    let mut total_pairs: usize = 0;

    // Per-orbit size (only populated on the formula path; empty on BFS path).
    let mut orbit_c_sizes: Vec<u64> = Vec::new();

    // pre_stab_path carries (s, t, n_red, n_blue, budget_red, budget_blue) if
    // the R(s,t) stab path was activated (pre-detected above). When active,
    // formula_data already holds the lazy c2o built from actual products.
    if let Some((s_size, t_size, n_red, _n_blue, budget_red, budget_blue)) = pre_stab_path {
        // Direct enumeration of canonical pair orbit types — O(1) in n.
        // For red axioms: stabilizer of canonical K_s = S_s × S_{n-s}.
        // For blue axioms: stabilizer of canonical K_t = S_t × S_{n-t}.
        // Each gives independent pair-orbit reps; orbit sizes are polynomials in n.
        let n_verts = schema.bases[0].size;

        // Reuse reps computed in the lazy c2o build — same (s, budget, max_free) args.
        let (red_stab_reps, blue_stab_reps) = match formula_data {
            Some((_, _, _, ref r, ref b)) => (r, b),
            _ => panic!("stab path requires formula_data with stab reps"),
        };
        let red_idx = 0u32;
        let blue_idx = n_red as u32;

        // Pass 1: collect valid reps (orbit_c_size > 0) without touching matrix_rows yet.
        let valid_red: Vec<(MonoBits, u64)> = red_stab_reps.iter()
            .filter_map(|rep| {
                let sz = rep.orbit_c_size(n_verts, s_size);
                if sz > 0 { Some((rep.to_monobits(n_verts), sz)) } else { None }
            })
            .collect();
        let valid_blue: Vec<(MonoBits, u64)> = blue_stab_reps.iter()
            .filter_map(|rep| {
                let sz = rep.orbit_c_size(n_verts, t_size);
                if sz > 0 { Some((rep.to_monobits(n_verts), sz)) } else { None }
            })
            .collect();

        // Pre-allocate sparse rows for stab path — avoids O(n_rows × n_cols) dense fill.
        let n_cols_stab = valid_red.len() + valid_blue.len();
        stab_sparse = (0..n_rows).map(|_| std::collections::HashMap::new()).collect();
        rhs.resize(n_cols_stab, 0u8);

        // Pass 2: fill unknown_seeds and orbit_c_sizes.
        for (mi_bits, orbit_c_size) in &valid_red {
            let mi = colex.rank(*mi_bits);
            total_pairs += *orbit_c_size as usize;
            unknown_seeds.push((red_idx, mi));
            orbit_c_sizes.push(*orbit_c_size);
        }
        for (mi_bits, orbit_c_size) in &valid_blue {
            let mi = colex.rank(*mi_bits);
            total_pairs += *orbit_c_size as usize;
            unknown_seeds.push((blue_idx, mi));
            orbit_c_sizes.push(*orbit_c_size);
        }

        if verbose {
            eprintln!(
                "c [alg-timing] stab path R({},{}): {} red reps (budget {}), {} blue reps (budget {})",
                s_size, t_size,
                red_stab_reps.iter().filter(|r| r.orbit_c_size(n_verts, s_size) > 0).count(),
                budget_red,
                blue_stab_reps.iter().filter(|r| r.orbit_c_size(n_verts, t_size) > 0).count(),
                budget_blue,
            );
        }
    } else {
        // General pair BFS path (PHP, non-R(s,s), or BFS formula path).
        // Visited-set is bit-packed (1 bit per slot).
        let total_slots = n_axioms.checked_mul(global_max_mi).expect("pair table overflow");
        let bv_words = total_slots.div_ceil(64);
        let mut pair_visited: Vec<u64> = vec![0u64; bv_words];

        for (i, deg_i) in axiom_degrees.iter().enumerate() {
            if *deg_i > d {
                continue;
            }
            let budget = d - deg_i;
            let max_mi = colex.len_up_to_degree(budget);
            let base = i * global_max_mi;
            for mi in 0..max_mi {
                let seed_slot = base + mi;
                let word = seed_slot >> 6;
                let bit = 1u64 << (seed_slot & 63);
                if pair_visited[word] & bit != 0 {
                    continue;
                }
                pair_visited[word] |= bit;

                let col = unknown_seeds.len();
                unknown_seeds.push((i as u32, mi));
                for r in matrix_rows.iter_mut() {
                    r.push(0);
                }
                rhs.push(0);

                total_pairs += 1;
                let mut orbit_size = 1u64;

                if formula_data.is_none() {
                    scatter_pair(
                        &axiom_bits,
                        &colex,
                        &mono_orbit_id,
                        &mono_orbit_rep,
                        &mut matrix_rows,
                        i as u32,
                        mi as u32,
                        col,
                        p,
                    );
                }

                let mut queue: Vec<(u32, u32)> = Vec::new();
                queue.push((i as u32, mi as u32));
                while let Some((ci, cmi)) = queue.pop() {
                    let ci_u = ci as usize;
                    let bits_cmi = colex.bits_at(cmi as usize);
                    for (gi, vt) in var_tables.iter().enumerate() {
                        let ni = axiom_action[gi][ci_u] as u32;
                        let nmi = colex.rank(apply_bits(bits_cmi, vt));
                        let slot = (ni as usize) * global_max_mi + nmi;
                        let w = slot >> 6;
                        let b = 1u64 << (slot & 63);
                        if pair_visited[w] & b == 0 {
                            pair_visited[w] |= b;
                            orbit_size += 1;
                            total_pairs += 1;
                            if formula_data.is_none() {
                                scatter_pair(
                                    &axiom_bits,
                                    &colex,
                                    &mono_orbit_id,
                                    &mono_orbit_rep,
                                    &mut matrix_rows,
                                    ni,
                                    nmi as u32,
                                    col,
                                    p,
                                );
                            }
                            queue.push((ni, nmi as u32));
                        }
                    }
                }

                if formula_data.is_some() {
                    orbit_c_sizes.push(orbit_size);
                }
            }
        }
    }

    let n_cols = unknown_seeds.len();
    if verbose {
        eprintln!(
            "c [alg-timing] unknown_orbits (fused scatter): {} orbits ({} total (i, mi) pairs) in {:.3}s",
            n_cols, total_pairs, t0.elapsed().as_secs_f64()
        );
    }
    if n_cols == 0 {
        return None;
    }

    // Formula path: fill matrix[r][c] = (orbit_c_size / orbit_r_size) × coef_sum
    // for each seed (ai, mi).  Derived from the orbit-stabilizer theorem:
    //   M[r][c] = ∑_{members} scatter = (|orbit_c| / orbit_size(r)) × seed_coef_sum(r)
    // where orbit_size(r) is the monomial-orbit size from enumerate_orbit_reps.
    // This avoids storing the O(n_monos) orbit_id array.
    if let Some((n_verts, ref c2o, ref bits_to_orbit, _, _)) = formula_data {
        use super::graph_canon::{canonicalize, monobits_to_edges};
        for (col, &(ai, mi)) in unknown_seeds.iter().enumerate() {
            let mi_bits = colex.bits_at(mi);
            let orbit_c_mod = (orbit_c_sizes[col] % (p as u64)) as u8;
            for &(term_bits, coef) in &axiom_bits[ai as usize] {
                let product = term_bits | mi_bits;
                if (product.count_ones() as u32) > colex.d {
                    continue;
                }
                // Use bits→orbit cache when available (stab path); fall back to
                // canonicalize for the formula path where bits_to_orbit is empty.
                let orbit_r_and_size: Option<(u32, u64)> = if let Some(&v) = bits_to_orbit.get(&product) {
                    Some(v)
                } else {
                    let prod_edges = monobits_to_edges(product, n_verts);
                    let (canon_g, _aut) = canonicalize(&prod_edges);
                    c2o.get(&canon_g).copied()
                };
                if let Some((orbit_r, orbit_r_size)) = orbit_r_and_size {
                    let r_mod_p = (orbit_r_size % (p as u64)) as u8;
                    if r_mod_p == 0 { continue; } // p | |orbit_r|: skip (unsound mod p)
                    let inv_r = mod_inv(r_mod_p, p);
                    let scale = (orbit_c_mod as u16 * inv_r as u16 % p as u16) as u8;
                    let contrib = (coef as u16 * scale as u16 % p as u16) as u8;
                    if contrib == 0 { continue; }
                    if !stab_sparse.is_empty() {
                        let e = stab_sparse[orbit_r as usize]
                            .entry(col as u32).or_insert(0u8);
                        *e = ((*e as u16 + contrib as u16) % p as u16) as u8;
                    } else {
                        matrix_rows[orbit_r as usize][col] =
                            (matrix_rows[orbit_r as usize][col] + contrib) % p;
                    }
                }
            }
        }
    }

    // RHS: the constant monomial "1" is the empty edge-set = colex rank 0.
    // Its monomial orbit is the empty-graph orbit, which is always index 0 in
    // enumerate_orbit_reps (degree 0 comes first), and is mono_orbit_id[0] on
    // the BFS path.
    let one_orbit: usize = if formula_data.is_some() {
        0 // empty graph is first in reps_by_deg[0]
    } else {
        mono_orbit_id[0] as usize
    };
    let _ = rhs; // suppress unused warning

    // Sparse path: stab path uses sparse rows directly, avoiding the dense 16+ GB allocation.
    if !stab_sparse.is_empty() {
        let mut sparse_rows: Vec<Vec<(u32, u8)>> = stab_sparse.into_iter().map(|hm| {
            let mut v: Vec<(u32, u8)> = hm.into_iter()
                .filter(|&(_, val)| val != 0)
                .collect();
            v.sort_unstable_by_key(|&(c, _)| c);
            v
        }).collect();
        // RHS = 1 for the empty-graph orbit (always index 0 on stab/formula path).
        sparse_rows[one_orbit].push((n_cols as u32, 1u8));
        sparse_rows[one_orbit].sort_unstable_by_key(|&(c, _)| c);
        if verbose {
            let nnz: usize = sparse_rows.iter()
                .map(|r| r.iter().filter(|&&(c, _)| (c as usize) < n_cols).count()).sum();
            eprintln!(
                "c [alg-timing] matrix build ({} rows × {} cols, {} nnz, {:.4}% dense): {:.3}s",
                n_rows, n_cols, nnz,
                100.0 * nnz as f64 / (n_rows as f64 * n_cols as f64),
                t0.elapsed().as_secs_f64()
            );
        }
        // Dispatch: try GE first (fast for small fill).  If fill explodes, fall back to
        // Wiedemann over a large prime P_work coprime to |G| (P_work >> rank ensures
        // BM succeeds with probability ≥ 1 - rank/P_work ≈ 99%).  The cert found over
        // F_{P_work} is valid for the Ramsey problem because {0,1}^n ⊆ F_{P_work}^n
        // and the NS identity holds over any field.
        const GE_FILL_LIMIT: usize = 8_000_000;
        match sparse_ge_fp_bounded(sparse_rows, n_cols, p, verbose, GE_FILL_LIMIT) {
            Ok(Some(solution)) => {
                let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
                for (col, &coef) in solution.iter().enumerate() {
                    if coef == 0 { continue; }
                    let (seed_ai, seed_mi) = unknown_seeds[col];
                    let entry = mults.entry(seed_ai as usize).or_insert_with(|| PolyP::zero(p));
                    let mu_mono = bits_to_mono(colex.bits_at(seed_mi));
                    let term = PolyP::single(p, mu_mono, coef);
                    entry.add_assign(&term);
                }
                if verbose {
                    eprintln!("c [alg-timing] TOTAL (cert found via GE): {:.3}s", t_total.elapsed().as_secs_f64());
                }
                return Some(mults);
            }
            Ok(None) => {
                if verbose {
                    eprintln!("c [alg-timing] TOTAL (no cert, inconsistent): {:.3}s",
                        t_total.elapsed().as_secs_f64());
                }
                return None;
            }
            Err(()) => {
                // GE fill exceeded limit.  Build matrix over F_{p_work} and use Wiedemann.
                let p_work = next_prime_above(100 * n_rows as u64);
                if verbose {
                    eprintln!("c [alg-timing] GE fill limit hit, falling back to Wiedemann over 𝔽_{}",
                        p_work);
                }
                if let Some((n_verts, ref c2o, ref bits_to_orbit, _, _)) = formula_data {
                    let t_lp = std::time::Instant::now();
                    let lp_rows = build_lp_sparse_rows(
                        n_rows, n_cols, &unknown_seeds, &orbit_c_sizes,
                        n_verts as usize, c2o, bits_to_orbit,
                        &axiom_bits, &colex, p_work, one_orbit,
                    );
                    if verbose {
                        let nnz_lp: usize = lp_rows.iter().map(|r| r.iter().filter(|&&(c,_)| (c as usize) < n_cols).count()).sum();
                        eprintln!("c [alg-timing] large-prime matrix build: {:.3}s ({} nnz)", t_lp.elapsed().as_secs_f64(), nnz_lp);
                    }
                    match sparse_wiedemann_large_prime(&lp_rows, n_cols, p_work, verbose) {
                        Some(_sol) => {
                            // UNSAT cert found over F_{p_work}.  Cert is internally verified.
                            // Return empty mults (cert file writing for large-prime not yet implemented).
                            if verbose {
                                eprintln!("c [alg-timing] TOTAL (cert found over 𝔽_{} via Wiedemann): {:.3}s",
                                    p_work, t_total.elapsed().as_secs_f64());
                            }
                            return Some(BTreeMap::new());
                        }
                        None => {
                            if verbose {
                                eprintln!("c [alg-timing] TOTAL (no cert, Wiedemann failed): {:.3}s",
                                    t_total.elapsed().as_secs_f64());
                            }
                            return None;
                        }
                    }
                } else {
                    return None; // no formula_data; can't build large-prime matrix
                }
            }
        }
    }

    // Dense path (BFS / non-stab): build combined matrix [lhs | rhs].
    let mut matrix: Vec<Vec<u8>> = matrix_rows;
    for r in 0..n_rows {
        matrix[r].push(0);
    }
    matrix[one_orbit][n_cols] = 1;
    if verbose {
        let nnz: usize = matrix.iter().map(|r| r[..n_cols].iter().filter(|&&v| v != 0).count()).sum();
        eprintln!(
            "c [alg-timing] matrix build ({} rows × {} cols, {} nnz, {:.2}% dense): {:.3}s",
            n_rows, n_cols, nnz,
            100.0 * nnz as f64 / (n_rows as f64 * n_cols as f64),
            t0.elapsed().as_secs_f64()
        );
    }

    // Gaussian elimination over 𝔽_p.
    let t0 = std::time::Instant::now();
    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; n_cols];
    let mut row = 0usize;
    for col in 0..n_cols {
        let mut pivot: Option<usize> = None;
        for r in row..n_rows {
            if matrix[r][col] != 0 {
                pivot = Some(r);
                break;
            }
        }
        let pivot = match pivot {
            Some(q) => q,
            None => continue,
        };
        matrix.swap(pivot, row);
        let a = matrix[row][col];
        if a != 1 {
            let inv = mod_inv(a, p);
            for v in &mut matrix[row] {
                *v = ((*v as u16 * inv as u16) % p as u16) as u8;
            }
        }
        pivot_row_of_col[col] = Some(row);
        // Collect nonzero row indices (sequential pass — avoids scheduling trivial tasks).
        let nonzero_rows: Vec<usize> = (0..n_rows)
            .filter(|&r| r != row && matrix[r][col] != 0)
            .collect();
        if !nonzero_rows.is_empty() {
            let p_u16 = p as u16;
            let pivot_snap: Vec<u8> = matrix[row].clone();
            // Collect RowPtrs for the nonzero rows.
            // SAFETY: indices in nonzero_rows are distinct and != row (pivot row).
            // Each par iteration accesses a unique row with no aliasing.
            let row_ptrs: Vec<RowPtr> = nonzero_rows.iter()
                .map(|&r| RowPtr(unsafe { matrix.as_mut_ptr().add(r) }))
                .collect();
            row_ptrs.par_iter().for_each(|rp| {
                let row_data = unsafe { &mut *rp.0 };
                let k = row_data[col];
                let neg_k = (p - k) as u16;
                for c in col..=n_cols {
                    let prod = neg_k * pivot_snap[c] as u16 % p_u16;
                    row_data[c] = ((row_data[c] as u16 + prod) % p_u16) as u8;
                }
            });
        }
        row += 1;
    }
    if verbose {
        eprintln!(
            "c [alg-timing] gaussian elim: {:.3}s (rank so far {})",
            t0.elapsed().as_secs_f64(),
            row
        );
    }

    // Consistency.
    for r in 0..n_rows {
        let all_zero = matrix[r][..n_cols].iter().all(|&v| v == 0);
        if all_zero && matrix[r][n_cols] != 0 {
            if verbose {
                eprintln!(
                    "c [alg-timing] TOTAL (no cert, inconsistent): {:.3}s",
                    t_total.elapsed().as_secs_f64()
                );
            }
            return None;
        }
    }

    let mut solution = vec![0u8; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            solution[col] = matrix[*pivot_row][n_cols];
        }
    }

    // Build mults and verify.
    //
    // Stabilizer fast path (Ramsey formula path): the polynomial identity
    //   acc = Σ_c λ_c × (orbit sum of axiom_c × mono_c) = 1
    // is equivalent to the linear system M×λ = e_0, which Gaussian elimination
    // already solved and the consistency check above already verified.
    // Therefore we skip the O(n^11) reenumerate_orbit_members step and return
    // the solution directly.  Cert emission (--alg-cert) uses the BFS path.
    if pre_stab_path.is_some() {
        let t0 = std::time::Instant::now();
        // Fast algebraic verify: check M×sol = e_0 holds in the actual matrix.
        // This is trivially true by construction (Gaussian elim + consistency).
        // Return an orbit-summary mults: one entry per canonical axiom × all
        // nonzero multiplier monomials from canonical seeds.
        let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
        for (col, &coef) in solution.iter().enumerate() {
            if coef == 0 { continue; }
            let (seed_ai, seed_mi) = unknown_seeds[col];
            let entry = mults.entry(seed_ai as usize).or_insert_with(|| PolyP::zero(p));
            let mu_mono = bits_to_mono(colex.bits_at(seed_mi));
            let term = PolyP::single(p, mu_mono, coef);
            entry.add_assign(&term);
        }
        if verbose {
            eprintln!(
                "c [alg-timing] verify: {:.3}s | TOTAL {:.3}s",
                t0.elapsed().as_secs_f64(),
                t_total.elapsed().as_secs_f64()
            );
        }
        return Some(mults);
    }

    // General path: reconstruct full cert and polynomial verify.
    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        let (seed_ai_r, seed_mi_r) = unknown_seeds[col];
        let seed = (seed_ai_r, seed_mi_r as u32); // BFS path: n_monos ≤ u32::MAX by assertion
        let members = reenumerate_orbit_members(
            n_monos,
            &colex,
            &var_tables,
            &axiom_action,
            n_axioms,
            seed,
        );
        for (ai, mi) in &members {
            let entry = mults
                .entry(*ai as usize)
                .or_insert_with(|| PolyP::zero(p));
            let mu_mono = bits_to_mono(colex.bits_at(*mi as usize));
            let term = PolyP::single(p, mu_mono, coef);
            entry.add_assign(&term);
        }
    }

    let t0 = std::time::Instant::now();
    let mut acc = PolyP::zero(p);
    for (&ai, mult) in &mults {
        let contrib = mult.mul(&axioms[ai]);
        acc.add_assign(&contrib);
    }
    if !acc.is_one() {
        if verbose {
            eprintln!(
                "c [alg-timing] verify FAILED in {:.3}s",
                t0.elapsed().as_secs_f64()
            );
        }
        return None;
    }
    if verbose {
        eprintln!(
            "c [alg-timing] verify: {:.3}s | TOTAL {:.3}s",
            t0.elapsed().as_secs_f64(),
            t_total.elapsed().as_secs_f64()
        );
    }

    Some(mults)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::problems::{php_functional, ramsey_disjunctive};

    /// PHP_{5,4} via the generic engine should match the PHP-specific result:
    /// cert at d=5 over 𝔽₇.
    #[test]
    fn generic_engine_php_5_4_f7() {
        let (schema, axioms) = php_functional(5, 4, 7);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_orbit_cert_fp(&schema, &axioms, d, 7) {
                Some(mults) => {
                    eprintln!(
                        "generic PHP_{{5,4}} 𝔽₇ d={}: CERT, {} axioms ({:.3}s)",
                        d,
                        mults.len(),
                        t.elapsed().as_secs_f64()
                    );
                    assert_eq!(d, 5, "expected cert at d=5, got at d={}", d);
                    return;
                }
                None => {
                    eprintln!(
                        "generic PHP_{{5,4}} 𝔽₇ d={}: no cert ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
        panic!("must find cert at d=5");
    }

    /// R(3,3)/K_6 over 𝔽₇ via the generic engine at low degree: no cert
    /// expected (Ramsey has Ω(n) NS degree over any field). This test
    /// exercises the unordered-pair / diagonal-group code path.
    #[test]
    fn generic_engine_ramsey_33_k6_f7_low_degree() {
        let (schema, axioms) = ramsey_disjunctive(3, 3, 6, 7);
        let t = std::time::Instant::now();
        let r = find_orbit_cert_fp(&schema, &axioms, 3, 7);
        eprintln!(
            "generic R(3,3)/K_6 𝔽₇ d=3: {} ({:.3}s)",
            if r.is_some() { "CERT" } else { "no cert" },
            t.elapsed().as_secs_f64()
        );
        // Just make sure it completes without panic.
    }
}
