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

/// Compute G-orbits of monomials via BFS over adjacent-transposition
/// generators. Returns `(orbit_id[i], orbit_rep[o])`.
fn monomial_orbits(
    schema: &TupleVarSchema,
    monomials: &[Monomial],
    gens: &[Generator],
) -> (Vec<usize>, Vec<usize>) {
    let index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();
    let n = monomials.len();
    let mut orbit_id = vec![usize::MAX; n];
    let mut orbit_rep: Vec<usize> = Vec::new();
    for start in 0..n {
        if orbit_id[start] != usize::MAX {
            continue;
        }
        let this_orbit = orbit_rep.len();
        orbit_id[start] = this_orbit;
        let mut rep = start;
        let mut queue = vec![start];
        while let Some(i) = queue.pop() {
            for g in gens {
                let img = schema.apply_mono(&monomials[i], g);
                let j = index[&img];
                if orbit_id[j] == usize::MAX {
                    orbit_id[j] = this_orbit;
                    if j < rep {
                        rep = j;
                    }
                    queue.push(j);
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
    let n = schema.n_vars();
    let gens = schema.generators();
    if axioms.is_empty() {
        return None;
    }

    // Monomial orbits.
    let monos = enumerate_up_to(n, d);
    let mono_index: BTreeMap<Monomial, usize> = monos
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();
    let (mono_orbit_id, mono_orbit_rep) = monomial_orbits(schema, &monos, &gens);
    let n_mono_orbits = mono_orbit_rep.len();

    // Axiom action under group.
    let axiom_action = axiom_action_table(schema, axioms, &gens);

    // Unknown orbits: (axiom_idx, multiplier_monomial) pairs under the group.
    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();
    let mut unknown_orbits: Vec<Vec<(usize, Monomial)>> = Vec::new();
    let mut pair_to_orbit: BTreeMap<(usize, Monomial), usize> = BTreeMap::new();

    for (i, deg_i) in axiom_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        let mus = enumerate_up_to(n, budget);
        for mu in mus {
            let key = (i, mu.clone());
            if pair_to_orbit.contains_key(&key) {
                continue;
            }
            let orbit_idx = unknown_orbits.len();
            let mut members: Vec<(usize, Monomial)> = Vec::new();
            let mut queue: Vec<(usize, Monomial)> = vec![key.clone()];
            pair_to_orbit.insert(key.clone(), orbit_idx);
            members.push(key.clone());
            while let Some((ci, cmu)) = queue.pop() {
                for (gi, g) in gens.iter().enumerate() {
                    let ni = axiom_action[gi][ci];
                    let nmu = schema.apply_mono(&cmu, g);
                    let nkey = (ni, nmu);
                    if !pair_to_orbit.contains_key(&nkey) {
                        pair_to_orbit.insert(nkey.clone(), orbit_idx);
                        members.push(nkey.clone());
                        queue.push(nkey);
                    }
                }
            }
            unknown_orbits.push(members);
        }
    }

    let n_rows = n_mono_orbits;
    let n_cols = unknown_orbits.len();
    if n_cols == 0 {
        return None;
    }

    // Dense u8 matrix; last column is RHS.
    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, members) in unknown_orbits.iter().enumerate() {
        // accum = ∑_{(i, μ) ∈ members} μ · axioms[i] — G-invariant.
        let mut accum = PolyP::zero(p);
        for (ai, mu) in members {
            let mu_poly = PolyP::single(p, mu.clone(), 1);
            let contrib = mu_poly.mul(&axioms[*ai]);
            accum.add_assign(&contrib);
        }
        // Project each G-invariant polynomial onto orbit rows by reading
        // coefficients at orbit representatives only.
        for (m, c) in &accum.terms {
            if let Some(&idx) = mono_index.get(m) {
                let row = mono_orbit_id[idx];
                if idx == mono_orbit_rep[row] {
                    matrix[row][col] = (matrix[row][col] + *c) % p;
                }
            }
        }
    }
    let one_idx = mono_index[&Monomial::one()];
    let one_orbit = mono_orbit_id[one_idx];
    matrix[one_orbit][n_cols] = 1;

    // Gaussian elimination over 𝔽_p.
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

    // Consistency.
    for r in 0..n_rows {
        let all_zero = matrix[r][..n_cols].iter().all(|&v| v == 0);
        if all_zero && matrix[r][n_cols] != 0 {
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
        for (ai, mu) in &unknown_orbits[col] {
            let entry = mults.entry(*ai).or_insert_with(|| PolyP::zero(p));
            let term = PolyP::single(p, mu.clone(), coef);
            entry.add_assign(&term);
        }
    }

    // Verify.
    let mut acc = PolyP::zero(p);
    for (&ai, mult) in &mults {
        let contrib = mult.mul(&axioms[ai]);
        acc.add_assign(&contrib);
    }
    if !acc.is_one() {
        return None;
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
