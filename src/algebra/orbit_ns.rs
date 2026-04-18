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
use std::collections::BTreeMap;

/// Fixed-capacity bitmask monomial representation. Bit `v-1` is set iff
/// variable `v` is in the monomial support. Keeps the engine in purely
/// integer arithmetic for monomial operations — no allocation per apply
/// or multiply.
///
/// 128-bit limit matches the u128 primitive. Falls back to the BTreeSet
/// path above for `n_vars > 128`; this covers PHP up to P·H = 128
/// (e.g. PHP_{11,11}, PHP_{13,9}) and Ramsey up to n=16 (120 edges).
type MonoBits = u128;

fn mono_to_bits(m: &Monomial, n: u32) -> MonoBits {
    debug_assert!(n <= 128);
    let mut b: MonoBits = 0;
    for &v in &m.0 {
        debug_assert!(v >= 1 && v <= n);
        b |= 1u128 << (v - 1);
    }
    b
}

fn bits_to_mono(mut b: MonoBits) -> Monomial {
    let mut s = std::collections::BTreeSet::new();
    while b != 0 {
        let lo = b.trailing_zeros();
        s.insert(lo + 1);
        b &= b - 1;
    }
    Monomial(s)
}

fn apply_bits(mut b: MonoBits, var_table: &[u32]) -> MonoBits {
    let mut out: MonoBits = 0;
    while b != 0 {
        let lo = b.trailing_zeros() as usize;
        out |= 1u128 << (var_table[lo + 1] - 1);
        b &= b - 1;
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

/// Enumerate multilinear monomials of degree ≤ `d` over `1..=n` directly as
/// u128 bitmasks, skipping the intermediate `Vec<Monomial>`. For large
/// monomial counts (PHP_{8,7} d=7 hits ~268M) this avoids a multi-GB
/// transient allocation of BTreeSet-backed Monomials.
///
/// The output is NOT sorted as `Monomial` comparison would sort it —
/// consumers that need canonical order should use `enumerate_up_to` or
/// sort separately. The current orbit-NS engine only uses hash-indexed
/// lookup, so sort order does not matter.
fn enumerate_bits_up_to(n: u32, d: usize) -> Vec<MonoBits> {
    fn rec(n: u32, start: u32, k_left: usize, bits: MonoBits, out: &mut Vec<MonoBits>) {
        if k_left == 0 {
            out.push(bits);
            return;
        }
        if n + 1 < start || (n - start + 1) < k_left as u32 {
            return;
        }
        for v in start..=n {
            rec(n, v + 1, k_left - 1, bits | (1u128 << (v - 1)), out);
        }
    }
    let mut out = Vec::new();
    for k in 0..=d {
        rec(n, 1, k, 0, &mut out);
    }
    out
}

/// Compute G-orbits of monomials from a precomputed per-generator monomial-
/// index action table. Pure integer BFS — no BTreeMap lookups. Returns
/// `(orbit_id[i], orbit_rep[o])`.
fn monomial_orbits_from_action(
    mono_action: &[Vec<u32>],
    n_monos: usize,
) -> (Vec<usize>, Vec<usize>) {
    let mut orbit_id = vec![usize::MAX; n_monos];
    let mut orbit_rep: Vec<usize> = Vec::new();
    let mut queue: Vec<u32> = Vec::new();
    for start in 0..n_monos {
        if orbit_id[start] != usize::MAX {
            continue;
        }
        let this_orbit = orbit_rep.len();
        orbit_id[start] = this_orbit;
        let mut rep = start;
        queue.clear();
        queue.push(start as u32);
        while let Some(i) = queue.pop() {
            for gi in 0..mono_action.len() {
                let j = mono_action[gi][i as usize] as usize;
                if orbit_id[j] == usize::MAX {
                    orbit_id[j] = this_orbit;
                    if j < rep {
                        rep = j;
                    }
                    queue.push(j as u32);
                }
            }
        }
        orbit_rep.push(rep);
    }
    (orbit_id, orbit_rep)
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
    monos_bits: &[MonoBits],
    bits_index: &std::collections::HashMap<MonoBits, usize>,
    mono_orbit_id: &[usize],
    mono_orbit_rep: &[usize],
    matrix: &mut [Vec<u8>],
    ai: u32,
    mi: u32,
    col: usize,
    p: u8,
) {
    let mu_bits = monos_bits[mi as usize];
    for &(term_bits, coef) in &axiom_bits[ai as usize] {
        let product = term_bits | mu_bits;
        if let Some(&idx) = bits_index.get(&product) {
            let row = mono_orbit_id[idx];
            if idx == mono_orbit_rep[row] {
                matrix[row][col] = (matrix[row][col] + coef) % p;
            }
        }
    }
}

/// Re-enumerate the full member list of an unknown-pair orbit starting
/// from its stored seed pair. Used during certificate reconstruction —
/// we don't materialize members during the main BFS to keep memory small.
fn reenumerate_orbit_members(
    n_monos: usize,
    axiom_action: &[Vec<usize>],
    mono_action: &[Vec<u32>],
    n_axioms: usize,
    seed: (u32, u32),
) -> Vec<(u32, u32)> {
    let total_slots = n_axioms * n_monos;
    let bv_words = total_slots.div_ceil(64);
    let mut visited: Vec<u64> = vec![0u64; bv_words];
    let seed_slot = (seed.0 as usize) * n_monos + seed.1 as usize;
    visited[seed_slot >> 6] |= 1u64 << (seed_slot & 63);
    let mut members: Vec<(u32, u32)> = vec![seed];
    let mut queue: Vec<(u32, u32)> = vec![seed];
    while let Some((ci, cmi)) = queue.pop() {
        let ci_u = ci as usize;
        let cmi_u = cmi as usize;
        for gi in 0..mono_action.len() {
            let ni = axiom_action[gi][ci_u] as u32;
            let nmi = mono_action[gi][cmi_u];
            let slot = (ni as usize) * n_monos + nmi as usize;
            let w = slot >> 6;
            let b = 1u64 << (slot & 63);
            if visited[w] & b == 0 {
                visited[w] |= b;
                members.push((ni, nmi));
                queue.push((ni, nmi));
            }
        }
    }
    members
}

/// Find a G-invariant NS certificate at degree `d` over 𝔽_p for the given
/// schema + axioms. Returns `axiom_idx → multiplier polynomial` on success.
///
/// Precondition: `p ∤ |G|`, otherwise invariant certs may not exist.
pub fn find_orbit_cert_fp(
    schema: &TupleVarSchema,
    axioms: &[PolyP],
    d: usize,
    p: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    let verbose = std::env::var("CASCADE_ALG_TIMING").is_ok();
    let t_total = std::time::Instant::now();
    let n = schema.n_vars();
    let gens = schema.generators();
    if axioms.is_empty() {
        return None;
    }

    assert!(
        n <= 128,
        "orbit_ns currently supports up to 128 vars (got {}). Bitmask Monomial \
         is u128; widen to [u64; 4] for larger families.",
        n
    );

    // Direct bit-packed monomial enumeration — skips the intermediate
    // Vec<Monomial>, which would be a multi-GB transient at PHP_{8,7} scale.
    let t0 = std::time::Instant::now();
    let monos_bits: Vec<MonoBits> = enumerate_bits_up_to(n, d);
    let n_monos = monos_bits.len();
    if verbose {
        eprintln!(
            "c [alg-timing] enumerate_bits_up_to: {} monomials in {:.3}s",
            n_monos,
            t0.elapsed().as_secs_f64()
        );
    }

    // Hash-indexed monomial lookup for O(1) image resolution during
    // mono_action and matrix scatter.
    let t0 = std::time::Instant::now();
    let mut bits_index: std::collections::HashMap<MonoBits, usize> =
        std::collections::HashMap::with_capacity(n_monos);
    for (i, &b) in monos_bits.iter().enumerate() {
        bits_index.insert(b, i);
    }
    if verbose {
        eprintln!(
            "c [alg-timing] mono_index build: {:.3}s",
            t0.elapsed().as_secs_f64()
        );
    }

    // Precompute per-generator var-action tables, then per-generator
    // monomial-index action tables. Uses u128 bit-apply — no allocation
    // per image lookup.
    let t0 = std::time::Instant::now();
    let var_tables: Vec<Vec<u32>> =
        gens.iter().map(|g| schema.var_action_table(g)).collect();
    let mono_action: Vec<Vec<u32>> = var_tables
        .iter()
        .map(|vt| {
            monos_bits
                .iter()
                .map(|&b| {
                    let img = apply_bits(b, vt);
                    *bits_index
                        .get(&img)
                        .expect("monomial image not in enumeration")
                        as u32
                })
                .collect()
        })
        .collect();
    if verbose {
        eprintln!(
            "c [alg-timing] mono_action table: {} gens × {} monos in {:.3}s",
            gens.len(),
            n_monos,
            t0.elapsed().as_secs_f64()
        );
    }

    // Monomial orbits via pure-index BFS using mono_action.
    let t0 = std::time::Instant::now();
    let (mono_orbit_id, mono_orbit_rep) =
        monomial_orbits_from_action(&mono_action, n_monos);
    let n_mono_orbits = mono_orbit_rep.len();
    if verbose {
        eprintln!(
            "c [alg-timing] monomial_orbits: {} orbits from {} monos in {:.3}s",
            n_mono_orbits,
            n_monos,
            t0.elapsed().as_secs_f64()
        );
    }

    // Axiom action under group.
    let t0 = std::time::Instant::now();
    let axiom_action = axiom_action_table(schema, axioms, &gens);
    if verbose {
        eprintln!(
            "c [alg-timing] axiom_action_table: {:.3}s",
            t0.elapsed().as_secs_f64()
        );
    }

    // Precompute axiom terms as (bits, coef) pairs — used by both the BFS
    // matrix scatter and the cert-reconstruction pass.
    let axiom_bits: Vec<Vec<(MonoBits, u8)>> = axioms
        .iter()
        .map(|a| {
            a.terms
                .iter()
                .map(|(m, c)| (mono_to_bits(m, n), *c))
                .collect()
        })
        .collect();

    // Unknown orbits: (axiom_idx, multiplier_mono_idx) pairs under the group.
    // Visited-set is bit-packed (1 bit per slot) — for PHP_{7,6} d=7 this
    // drops the dedup table from 17 GB (Vec<u32>) to ~550 MB. Member lists
    // are NOT materialized: as each pair is discovered we scatter its
    // axiom-term contributions straight into the matrix, and we keep only
    // one canonical seed per orbit for later cert reconstruction.
    let t0 = std::time::Instant::now();
    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();
    let n_axioms = axioms.len();
    let total_slots = n_axioms.checked_mul(n_monos).expect("pair table overflow");
    let bv_words = total_slots.div_ceil(64);
    let mut pair_visited: Vec<u64> = vec![0u64; bv_words];
    // Seed of each unknown orbit (first pair that started its BFS) — enough
    // to re-enumerate members on demand during cert reconstruction.
    let mut unknown_seeds: Vec<(u32, u32)> = Vec::new();

    let n_rows = n_mono_orbits;

    // Matrix grows column-by-column as orbits are discovered. Row-major
    // storage so Gaussian elimination works unchanged on the final shape.
    let mut matrix_rows: Vec<Vec<u8>> = (0..n_rows).map(|_| Vec::new()).collect();
    let mut rhs: Vec<u8> = Vec::new();

    // Counters for timing summary.
    let mut total_pairs: usize = 0;

    for (i, deg_i) in axiom_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        let base = i * n_monos;
        for (mi, &bits) in monos_bits.iter().enumerate() {
            if (bits.count_ones() as usize) > budget {
                continue;
            }
            let seed_slot = base + mi;
            let word = seed_slot >> 6;
            let bit = 1u64 << (seed_slot & 63);
            if pair_visited[word] & bit != 0 {
                continue;
            }
            pair_visited[word] |= bit;

            let col = unknown_seeds.len();
            unknown_seeds.push((i as u32, mi as u32));
            // Extend matrix with a fresh zero column.
            for r in matrix_rows.iter_mut() {
                r.push(0);
            }
            rhs.push(0);

            // Scatter seed pair.
            scatter_pair(
                &axiom_bits,
                &monos_bits,
                &bits_index,
                &mono_orbit_id,
                &mono_orbit_rep,
                &mut matrix_rows,
                i as u32,
                mi as u32,
                col,
                p,
            );
            total_pairs += 1;

            let mut queue: Vec<(u32, u32)> = Vec::new();
            queue.push((i as u32, mi as u32));
            while let Some((ci, cmi)) = queue.pop() {
                let ci_u = ci as usize;
                let cmi_u = cmi as usize;
                for gi in 0..gens.len() {
                    let ni = axiom_action[gi][ci_u] as u32;
                    let nmi = mono_action[gi][cmi_u];
                    let slot = (ni as usize) * n_monos + nmi as usize;
                    let w = slot >> 6;
                    let b = 1u64 << (slot & 63);
                    if pair_visited[w] & b == 0 {
                        pair_visited[w] |= b;
                        scatter_pair(
                            &axiom_bits,
                            &monos_bits,
                            &bits_index,
                            &mono_orbit_id,
                            &mono_orbit_rep,
                            &mut matrix_rows,
                            ni,
                            nmi,
                            col,
                            p,
                        );
                        queue.push((ni, nmi));
                        total_pairs += 1;
                    }
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
    drop(pair_visited);
    if n_cols == 0 {
        return None;
    }

    // RHS: mono_rep[one_orbit] = 1. Place into matrix_rows + rhs.
    let one_idx = bits_index[&0u128];
    let one_orbit = mono_orbit_id[one_idx];
    rhs[0] = rhs[0]; // keep types stable (no-op)
    // Build the combined matrix [lhs | rhs] expected by the existing
    // Gaussian elim (row-major, last column is RHS).
    let mut matrix: Vec<Vec<u8>> = matrix_rows;
    for r in 0..n_rows {
        matrix[r].push(0);
    }
    matrix[one_orbit][n_cols] = 1;
    // Dummy use of rhs to silence unused warning — keeps symmetry with the
    // bookkeeping above and makes it easy to switch to a split layout.
    let _ = rhs;
    if verbose {
        eprintln!(
            "c [alg-timing] matrix build ({} rows × {} cols): {:.3}s",
            n_rows,
            n_cols,
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
        for r in 0..n_rows {
            if r == row {
                continue;
            }
            let k = matrix[r][col];
            if k == 0 {
                continue;
            }
            let neg_k = p - k;
            for c in col..=n_cols {
                let prod = (neg_k as u16 * matrix[row][c] as u16) % p as u16;
                matrix[r][c] = ((matrix[r][c] as u16 + prod) % p as u16) as u8;
            }
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

    // Reconstruct full cert. Member lists were not stored during BFS (to
    // keep memory small); re-enumerate each selected orbit from its seed.
    // Only orbits with nonzero solution coefficients are walked.
    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        let seed = unknown_seeds[col];
        let members = reenumerate_orbit_members(
            n_monos,
            &axiom_action,
            &mono_action,
            n_axioms,
            seed,
        );
        for (ai, mi) in &members {
            let entry = mults
                .entry(*ai as usize)
                .or_insert_with(|| PolyP::zero(p));
            let mu_mono = bits_to_mono(monos_bits[*mi as usize]);
            let term = PolyP::single(p, mu_mono, coef);
            entry.add_assign(&term);
        }
    }

    // Verify.
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
