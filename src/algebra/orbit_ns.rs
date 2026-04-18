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

    // Monomial enumeration (produces Monomial; converted to bits below).
    let t0 = std::time::Instant::now();
    let monos = enumerate_up_to(n, d);
    let n_monos = monos.len();
    if verbose {
        eprintln!(
            "c [alg-timing] enumerate_up_to: {} monomials in {:.3}s",
            n_monos,
            t0.elapsed().as_secs_f64()
        );
    }

    // Bit-packed monomials + O(1) index. Keeping the engine in u128 space
    // eliminates per-operation BTreeSet allocations — critical for matrix
    // build and mono_action, which dominate at higher degree.
    let t0 = std::time::Instant::now();
    let monos_bits: Vec<MonoBits> =
        monos.iter().map(|m| mono_to_bits(m, n)).collect();
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

    // Unknown orbits: (axiom_idx, multiplier_mono_idx) pairs under the group.
    // Key space is axioms.len() × monos.len(); packed as axiom_idx*n_monos + mi.
    // `pair_orbit[key] = orbit_idx+1` (0 = unvisited) — a single u32 per pair.
    let t0 = std::time::Instant::now();
    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();
    let n_monos = monos.len();
    let n_axioms = axioms.len();
    let total_slots = n_axioms.checked_mul(n_monos).expect("pair table overflow");
    let mut pair_orbit: Vec<u32> = vec![0u32; total_slots];
    let mut unknown_orbits: Vec<Vec<(u32, u32)>> = Vec::new();

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
            if pair_orbit[base + mi] != 0 {
                continue;
            }
            let orbit_idx = unknown_orbits.len() as u32;
            let tag = orbit_idx + 1;
            pair_orbit[base + mi] = tag;
            let mut members: Vec<(u32, u32)> = Vec::new();
            members.push((i as u32, mi as u32));
            let mut queue: Vec<(u32, u32)> = Vec::new();
            queue.push((i as u32, mi as u32));
            while let Some((ci, cmi)) = queue.pop() {
                let ci_u = ci as usize;
                let cmi_u = cmi as usize;
                for gi in 0..gens.len() {
                    let ni = axiom_action[gi][ci_u] as u32;
                    let nmi = mono_action[gi][cmi_u];
                    let slot = (ni as usize) * n_monos + nmi as usize;
                    if pair_orbit[slot] == 0 {
                        pair_orbit[slot] = tag;
                        members.push((ni, nmi));
                        queue.push((ni, nmi));
                    }
                }
            }
            unknown_orbits.push(members);
        }
    }

    let n_rows = n_mono_orbits;
    let n_cols = unknown_orbits.len();
    if verbose {
        let total_members: usize = unknown_orbits.iter().map(|m| m.len()).sum();
        eprintln!(
            "c [alg-timing] unknown_orbits: {} orbits ({} total (i, mi) pairs) in {:.3}s",
            n_cols,
            total_members,
            t0.elapsed().as_secs_f64()
        );
    }
    drop(pair_orbit); // free before matrix build
    if n_cols == 0 {
        return None;
    }

    // Precompute axiom terms as (bits, coef) pairs — avoids re-converting
    // Monomial → bits per member during matrix build.
    let axiom_bits: Vec<Vec<(MonoBits, u8)>> = axioms
        .iter()
        .map(|a| {
            a.terms
                .iter()
                .map(|(m, c)| (mono_to_bits(m, n), *c))
                .collect()
        })
        .collect();

    // Dense u8 matrix; last column is RHS. Populated by scattering μ·axiom_i
    // contributions directly into orbit-representative rows. Entire hot loop
    // runs in u128 bitmask space — no per-step allocation.
    let t0 = std::time::Instant::now();
    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, members) in unknown_orbits.iter().enumerate() {
        for (ai, mi) in members {
            let mu_bits = monos_bits[*mi as usize];
            for &(term_bits, coef) in &axiom_bits[*ai as usize] {
                let product = term_bits | mu_bits;
                if let Some(&idx) = bits_index.get(&product) {
                    let row = mono_orbit_id[idx];
                    if idx == mono_orbit_rep[row] {
                        matrix[row][col] = (matrix[row][col] + coef) % p;
                    }
                }
            }
        }
    }
    let one_idx = bits_index[&0u128];
    let one_orbit = mono_orbit_id[one_idx];
    matrix[one_orbit][n_cols] = 1;
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

    // Reconstruct full cert.
    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        for (ai, mi) in &unknown_orbits[col] {
            let entry = mults
                .entry(*ai as usize)
                .or_insert_with(|| PolyP::zero(p));
            let term = PolyP::single(p, monos[*mi as usize].clone(), coef);
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
