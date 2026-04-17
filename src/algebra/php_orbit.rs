//! PHP-specific orbit-reduced Nullstellensatz.
//!
//! Two variants:
//!
//! * **𝔽₂ CNF** ([`find_php_orbit_cert`]) — documents the negative result:
//!   PHP has no G-invariant cert over 𝔽₂ at low degree because |G| = P!·H!
//!   is even, so symmetrization gives the zero certificate.
//!
//! * **𝔽_p functional** ([`find_php_functional_orbit_cert_fp`]) — the real
//!   win. Uses linear totality axioms (`∑_h x(p,h) − 1 = 0`) and requires
//!   `p ∤ |G|`, which makes G-invariant certs exist whenever any cert
//!   exists. Both rows (monomials) and columns (unknowns) collapse by
//!   G-orbit — for PHP_{10,9} at d=3 the monomial count goes from 121,576
//!   to ~10 orbits, a 12,000× reduction.
//!
//! # Group action
//!
//! Variables: `var(p, h) = (p-1) * H + h` for p ∈ 1..=P, h ∈ 1..=H.
//! `(σ, τ) · x(p, h) = x(σ(p), τ(h))`.
//! A monomial is a subset of variables = a bipartite graph on [P] + [H].
//! Orbits of monomials are bipartite-graph isomorphism classes.

use super::ns::{CertTerm, NsCertificate, NsResult};
use super::poly::{Monomial, Poly};
use std::collections::{BTreeMap, BTreeSet};

/// A PHP_{P,H} instance: P pigeons, H holes. UNSAT iff P > H.
#[derive(Clone, Copy, Debug)]
pub struct Php {
    pub n_pigeons: u32,
    pub n_holes: u32,
}

impl Php {
    pub fn new(n_pigeons: u32, n_holes: u32) -> Self {
        Self { n_pigeons, n_holes }
    }

    pub fn n_vars(&self) -> u32 {
        self.n_pigeons * self.n_holes
    }

    pub fn var(&self, p: u32, h: u32) -> u32 {
        (p - 1) * self.n_holes + h
    }

    pub fn decode(&self, v: u32) -> (u32, u32) {
        let p = (v - 1) / self.n_holes + 1;
        let h = (v - 1) % self.n_holes + 1;
        (p, h)
    }

    /// PHP clauses: pigeon totality (P clauses of width H) + AMO per hole
    /// (H · C(P, 2) clauses of width 2).
    pub fn clauses(&self) -> Vec<Vec<i32>> {
        let mut out = Vec::new();
        for p in 1..=self.n_pigeons {
            let mut c = Vec::new();
            for h in 1..=self.n_holes {
                c.push(self.var(p, h) as i32);
            }
            out.push(c);
        }
        for h in 1..=self.n_holes {
            for p1 in 1..=self.n_pigeons {
                for p2 in (p1 + 1)..=self.n_pigeons {
                    out.push(vec![
                        -(self.var(p1, h) as i32),
                        -(self.var(p2, h) as i32),
                    ]);
                }
            }
        }
        out
    }

    /// Apply (σ, τ) to variable v. σ, τ are 0-indexed permutation vectors
    /// (so σ[i] = where pigeon i+1 goes, minus 1).
    pub fn apply_var(&self, v: u32, sigma: &[u32], tau: &[u32]) -> u32 {
        let (p, h) = self.decode(v);
        let new_p = sigma[(p - 1) as usize] + 1;
        let new_h = tau[(h - 1) as usize] + 1;
        self.var(new_p, new_h)
    }

    pub fn apply_mono(&self, m: &Monomial, sigma: &[u32], tau: &[u32]) -> Monomial {
        let mut s = BTreeSet::new();
        for &v in &m.0 {
            s.insert(self.apply_var(v, sigma, tau));
        }
        Monomial(s)
    }

    /// Adjacent-transposition generators for S_P × S_H: pigeon swaps
    /// (i, i+1) and hole swaps (j, j+1).
    pub fn generators(&self) -> Vec<(Vec<u32>, Vec<u32>)> {
        let id_p: Vec<u32> = (0..self.n_pigeons).collect();
        let id_h: Vec<u32> = (0..self.n_holes).collect();
        let mut gens = Vec::new();
        for i in 0..self.n_pigeons.saturating_sub(1) {
            let mut s = id_p.clone();
            s.swap(i as usize, (i + 1) as usize);
            gens.push((s, id_h.clone()));
        }
        for j in 0..self.n_holes.saturating_sub(1) {
            let mut t = id_h.clone();
            t.swap(j as usize, (j + 1) as usize);
            gens.push((id_p.clone(), t));
        }
        gens
    }
}

/// Enumerate all multilinear monomials of degree exactly `k` on `n` vars.
fn enumerate_monomials_of_degree(n: u32, k: usize) -> Vec<Monomial> {
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

fn enumerate_monomials_up_to(n: u32, d: usize) -> Vec<Monomial> {
    let mut out = Vec::new();
    for k in 0..=d {
        out.extend(enumerate_monomials_of_degree(n, k));
    }
    out.sort();
    out
}

/// Partition monomials into G-orbits using BFS from adjacent-transposition
/// generators. Returns:
/// * `orbit_id[i]` = orbit index of `monomials[i]`.
/// * `orbit_rep[o]` = index into `monomials` of the canonical rep (lex-smallest).
pub fn compute_monomial_orbits(
    instance: &Php,
    monomials: &[Monomial],
) -> (Vec<usize>, Vec<usize>) {
    let index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();
    let gens = instance.generators();
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
            for (sigma, tau) in &gens {
                let img = instance.apply_mono(&monomials[i], sigma, tau);
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

/// An unknown in the G-invariant NS system: a (clause-orbit, multiplier-mono)
/// pair. The clause-orbit tells us which clause type (pigeon vs AMO), and
/// the multiplier-mono orbit gives the multiplier polynomial structure.
///
/// Rather than enumerate all (i, μ) pairs and collapse by orbit, we directly
/// enumerate orbit representatives by picking a "canonical" clause instance:
/// * Pigeon clause: always pigeon 1. Multiplier μ ∈ any multilinear monomial
///   of degree ≤ d - H.
/// * AMO clause: always h=1, p1=1, p2=2. Multiplier μ ∈ any multilinear
///   monomial of degree ≤ d - 2.
///
/// Two reps (i₁, μ₁) and (i₂, μ₂) lie in the same G-orbit iff there's g with
/// g·(i₁, μ₁) = (i₂, μ₂). We enumerate by picking canonical reps via
/// "G-orbit under the stabilizer of i₁". For the pigeon-1 case, the
/// stabilizer of pigeon 1 in S_P × S_H is S_{P-1} × S_H (permutes pigeons
/// 2..P and any hole). For AMO {h=1, p1=1, p2=2}, the stabilizer is
/// { (σ, τ) : σ({1,2}) = {1,2}, τ(1) = 1 } = {id, (1 2)}_P × S_{P-2} × S_{H-1}.
///
/// We enumerate unknowns as (canonical clause rep, orbit of μ under clause-stab).
#[derive(Clone, Debug)]
pub enum ClauseKind {
    Pigeon,
    Amo,
}

#[derive(Clone, Debug)]
pub struct UnknownOrbit {
    pub kind: ClauseKind,
    /// Multiplier monomial representative (lex-smallest under the
    /// stabilizer of the clause rep).
    pub mu_rep: Monomial,
    /// All (i, μ) pairs in this orbit. Used to build the full cert.
    pub members: Vec<(usize, Monomial)>,
}

/// Build the full NS certificate search as an orbit-reduced linear system.
/// Returns a G-invariant cert if found.
pub fn find_php_orbit_cert(instance: &Php, d: usize) -> NsResult {
    let n = instance.n_vars();
    let clauses = instance.clauses();
    let clause_polys: Vec<Poly> = clauses.iter().map(|c| Poly::clause_poly(c)).collect();
    let clause_degrees: Vec<usize> = clause_polys.iter().map(|p| p.degree()).collect();

    // Map clause index → ClauseKind.
    let n_pigeon_clauses = instance.n_pigeons as usize;
    let clause_kind = |i: usize| -> ClauseKind {
        if i < n_pigeon_clauses {
            ClauseKind::Pigeon
        } else {
            ClauseKind::Amo
        }
    };

    // Step 1: monomial orbits up to degree d.
    let monomials = enumerate_monomials_up_to(n, d);
    let mono_index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();
    let (mono_orbit_id, mono_orbit_rep) = compute_monomial_orbits(instance, &monomials);
    let n_mono_orbits = mono_orbit_rep.len();

    // Step 2: enumerate unknowns per orbit.
    // Approach: for each (clause_idx, multiplier_monomial), determine its
    // G-orbit via the pair's canonical form. Two pairs are in the same
    // orbit iff there is g ∈ G mapping one to the other.
    //
    // Canonical form algorithm: given (i, μ), enumerate the full G-orbit
    // by BFS over generators on pairs. Keep canonical (lex-smallest) pair.
    let mut unknown_orbits: Vec<UnknownOrbit> = Vec::new();
    let mut pair_to_orbit: BTreeMap<(usize, Monomial), usize> = BTreeMap::new();

    let gens = instance.generators();

    let apply_pair = |i: usize,
                      mu: &Monomial,
                      sigma: &[u32],
                      tau: &[u32]|
     -> (usize, Monomial) {
        // New clause index under (σ, τ).
        let new_i = match clause_kind(i) {
            ClauseKind::Pigeon => {
                // clause_polys[i] is the pigeon-totality clause for some pigeon p = i+1.
                // Under (σ, τ): goes to clause for pigeon σ(p).
                let p = (i as u32) + 1; // 1-indexed pigeon
                let new_p = sigma[(p - 1) as usize] + 1;
                (new_p - 1) as usize
            }
            ClauseKind::Amo => {
                // AMO clause index: after pigeon clauses, we have AMO clauses
                // indexed by (h, p1, p2) with p1 < p2.
                // Layout: for h ∈ [H], for p1<p2 ∈ [P]×[P]: AMO(h, p1, p2).
                let amo_idx = i - n_pigeon_clauses;
                let p_choose_2 = ((instance.n_pigeons) * (instance.n_pigeons - 1) / 2) as usize;
                let h = (amo_idx / p_choose_2) as u32 + 1;
                let local = amo_idx % p_choose_2;
                // Convert `local` to (p1, p2) with p1 < p2.
                let (p1, p2) = pair_index_to_pair(local, instance.n_pigeons);
                let new_h = tau[(h - 1) as usize] + 1;
                let np1 = sigma[(p1 - 1) as usize] + 1;
                let np2 = sigma[(p2 - 1) as usize] + 1;
                let (np1, np2) = if np1 < np2 { (np1, np2) } else { (np2, np1) };
                let new_local = pair_to_pair_index(np1, np2, instance.n_pigeons);
                n_pigeon_clauses + ((new_h - 1) as usize) * p_choose_2 + new_local
            }
        };
        let new_mu = instance.apply_mono(mu, sigma, tau);
        (new_i, new_mu)
    };

    for (i, deg_i) in clause_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        let mus = enumerate_monomials_up_to(n, budget);
        for mu in mus {
            let key = (i, mu.clone());
            if pair_to_orbit.contains_key(&key) {
                continue;
            }
            // BFS on (i, μ) orbit.
            let orbit_idx = unknown_orbits.len();
            let kind = clause_kind(i);
            let mut members: Vec<(usize, Monomial)> = Vec::new();
            let mut rep: Monomial = mu.clone();
            let mut queue: Vec<(usize, Monomial)> = vec![key.clone()];
            pair_to_orbit.insert(key.clone(), orbit_idx);
            members.push(key.clone());
            while let Some((ci, cmu)) = queue.pop() {
                for (sigma, tau) in &gens {
                    let nxt = apply_pair(ci, &cmu, sigma, tau);
                    if !pair_to_orbit.contains_key(&nxt) {
                        pair_to_orbit.insert(nxt.clone(), orbit_idx);
                        if nxt.1 < rep {
                            rep = nxt.1.clone();
                        }
                        members.push(nxt.clone());
                        queue.push(nxt);
                    }
                }
            }
            unknown_orbits.push(UnknownOrbit {
                kind,
                mu_rep: rep,
                members,
            });
        }
    }
    let n_unknowns = unknown_orbits.len();

    // Step 3: build reduced matrix.
    // Rows: one per monomial orbit (indexed by mono_orbit_rep).
    // Cols: one per unknown orbit + 1 for RHS.
    // Entry[row][col] = sum over members (i, μ) of [rep_mono ∈ μ · P_i] mod 2.
    // RHS: 1 for row = orbit of empty mono.
    let n_rows = n_mono_orbits;
    let n_cols = n_unknowns;
    let words_per_row = (n_cols + 1 + 63) / 64;
    let mut matrix: Vec<Vec<u64>> = vec![vec![0u64; words_per_row]; n_rows];

    // Pre-pick a monomial rep per orbit row for fast membership test.
    let mono_orbit_rep_mono: Vec<Monomial> = mono_orbit_rep
        .iter()
        .map(|&idx| monomials[idx].clone())
        .collect();

    // For each unknown orbit, expand its (clause × multiplier) products and
    // accumulate XOR contributions on the monomial-orbit rows.
    for (col, uk) in unknown_orbits.iter().enumerate() {
        for (i, mu) in &uk.members {
            // Product μ · P_i, expanded.
            let mu_poly = {
                let mut s = BTreeSet::new();
                s.insert(mu.clone());
                Poly(s)
            };
            let prod = mu_poly.mul(&clause_polys[*i]);
            for m in &prod.0 {
                // Find m's orbit.
                let row = if let Some(&idx) = mono_index.get(m) {
                    mono_orbit_id[idx]
                } else {
                    // Exceeds degree d — shouldn't happen given budgeting.
                    continue;
                };
                let word = col >> 6;
                let bit = col & 63;
                matrix[row][word] ^= 1u64 << bit;
            }
        }
    }
    // RHS.
    let rhs_col = n_cols;
    let rhs_word = rhs_col >> 6;
    let rhs_bit = rhs_col & 63;
    let one_idx = mono_index[&Monomial::one()];
    let one_orbit = mono_orbit_id[one_idx];
    matrix[one_orbit][rhs_word] |= 1u64 << rhs_bit;

    // Step 4: Gaussian elimination over 𝔽₂.
    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; n_cols];
    let mut row = 0usize;
    for col in 0..n_cols {
        let col_word = col >> 6;
        let col_bit = 1u64 << (col & 63);
        let mut pivot: Option<usize> = None;
        for r in row..n_rows {
            if matrix[r][col_word] & col_bit != 0 {
                pivot = Some(r);
                break;
            }
        }
        let pivot = match pivot {
            Some(p) => p,
            None => continue,
        };
        matrix.swap(pivot, row);
        pivot_row_of_col[col] = Some(row);
        for r in 0..n_rows {
            if r == row {
                continue;
            }
            if matrix[r][col_word] & col_bit != 0 {
                for w in 0..words_per_row {
                    matrix[r][w] ^= matrix[row][w];
                }
            }
        }
        row += 1;
    }

    // Consistency check.
    for r in 0..n_rows {
        let mut all_zero_lhs = true;
        for c in 0..n_cols {
            let w = c >> 6;
            let b = 1u64 << (c & 63);
            if matrix[r][w] & b != 0 {
                all_zero_lhs = false;
                break;
            }
        }
        if all_zero_lhs {
            let has_rhs = matrix[r][rhs_word] & (1u64 << rhs_bit) != 0;
            if has_rhs {
                return NsResult::NoCertificate;
            }
        }
    }

    // Solution: free = 0, pivot = RHS.
    let mut solution = vec![false; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            let has_rhs = matrix[*pivot_row][rhs_word] & (1u64 << rhs_bit) != 0;
            solution[col] = has_rhs;
        }
    }

    // Build certificate: for each selected orbit, include all (i, μ) in orbit.
    let mut mults: BTreeMap<usize, Poly> = BTreeMap::new();
    for (col, val) in solution.iter().enumerate() {
        if !*val {
            continue;
        }
        for (i, mu) in &unknown_orbits[col].members {
            let entry = mults.entry(*i).or_insert_with(Poly::zero);
            let mu_poly = {
                let mut s = BTreeSet::new();
                s.insert(mu.clone());
                Poly(s)
            };
            entry.add_assign(&mu_poly);
        }
    }

    let mut terms: Vec<CertTerm> = mults
        .into_iter()
        .filter(|(_, p)| !p.is_zero())
        .map(|(clause_idx, multiplier)| CertTerm {
            clause_idx,
            multiplier,
        })
        .collect();
    terms.sort_by_key(|t| t.clause_idx);

    if terms.is_empty() {
        return NsResult::NoCertificate;
    }
    NsResult::Unsat(NsCertificate { degree: d, terms })
}

/// Convert 0-indexed pair-index to (p1, p2) with 1 ≤ p1 < p2 ≤ P.
/// Layout: pairs in lex order (1,2), (1,3), ..., (1,P), (2,3), ..., (P-1,P).
fn pair_index_to_pair(idx: usize, p: u32) -> (u32, u32) {
    let mut remain = idx;
    for p1 in 1..p {
        let width = (p - p1) as usize;
        if remain < width {
            return (p1, p1 + 1 + remain as u32);
        }
        remain -= width;
    }
    unreachable!("pair_index out of range")
}

/// Inverse of pair_index_to_pair.
fn pair_to_pair_index(p1: u32, p2: u32, p: u32) -> usize {
    assert!(p1 < p2);
    let mut idx = 0usize;
    for x in 1..p1 {
        idx += (p - x) as usize;
    }
    idx += (p2 - p1 - 1) as usize;
    idx
}

// ---------------------------------------------------------------------
// Orbit-reduced NS over 𝔽_p with functional PHP axioms.
// ---------------------------------------------------------------------

use super::ns_fp::PolyP;

/// Axiom layout for functional PHP encoding:
/// * Indices `0..P`: pigeon-totality axiom for pigeon p+1, linear
///   `∑_h x(p+1, h) − 1`.
/// * Indices `P..P+H·C(P,2)`: AMO axiom for (h, p1, p2) (same layout as
///   [`Php::clauses`]), quadratic `x(p1, h) · x(p2, h)`.
pub fn php_functional_axioms_for_fp(instance: &Php, p_prime: u8) -> Vec<PolyP> {
    let var = |pp: u32, hh: u32| -> u32 { (pp - 1) * instance.n_holes + hh };
    let mut out = Vec::new();
    for pp in 1..=instance.n_pigeons {
        let mut terms = BTreeMap::new();
        for hh in 1..=instance.n_holes {
            terms.insert(Monomial::single(var(pp, hh)), 1u8);
        }
        terms.insert(Monomial::one(), p_prime - 1);
        out.push(PolyP {
            p: p_prime,
            terms,
        });
    }
    for hh in 1..=instance.n_holes {
        for p1 in 1..=instance.n_pigeons {
            for p2 in (p1 + 1)..=instance.n_pigeons {
                let m = Monomial::from_vars([var(p1, hh), var(p2, hh)]);
                let mut terms = BTreeMap::new();
                terms.insert(m, 1u8);
                out.push(PolyP {
                    p: p_prime,
                    terms,
                });
            }
        }
    }
    out
}

/// Find a G-invariant NS certificate for PHP_{P,H} over 𝔽_p at degree `d`
/// using the functional axiom encoding. Soundness condition: `p ∤ |G|` —
/// i.e., `p ∤ P!·H!`. When that holds, a G-invariant cert exists iff any
/// cert does. For convenience we accept the prime without checking; for
/// PHP_{10,9} use p = 11 or 13.
pub fn find_php_functional_orbit_cert_fp(
    instance: &Php,
    d: usize,
    p: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    let n = instance.n_vars();
    let axioms = php_functional_axioms_for_fp(instance, p);
    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();

    let n_pigeon_axioms = instance.n_pigeons as usize;

    // Monomial orbits.
    let monomials = enumerate_monomials_up_to(n, d);
    let mono_index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();
    let (mono_orbit_id, mono_orbit_rep) = compute_monomial_orbits(instance, &monomials);
    let n_mono_orbits = mono_orbit_rep.len();

    // Apply group element to axiom index: same logic as the 𝔽₂ orbit code.
    let gens = instance.generators();
    let p_choose_2 =
        ((instance.n_pigeons) * (instance.n_pigeons - 1) / 2) as usize;

    let apply_axiom = |i: usize, sigma: &[u32], tau: &[u32]| -> usize {
        if i < n_pigeon_axioms {
            let pp = (i as u32) + 1;
            let new_pp = sigma[(pp - 1) as usize] + 1;
            (new_pp - 1) as usize
        } else {
            let amo_idx = i - n_pigeon_axioms;
            let hh = (amo_idx / p_choose_2) as u32 + 1;
            let local = amo_idx % p_choose_2;
            let (p1, p2) = pair_index_to_pair(local, instance.n_pigeons);
            let new_h = tau[(hh - 1) as usize] + 1;
            let np1 = sigma[(p1 - 1) as usize] + 1;
            let np2 = sigma[(p2 - 1) as usize] + 1;
            let (np1, np2) = if np1 < np2 { (np1, np2) } else { (np2, np1) };
            let new_local = pair_to_pair_index(np1, np2, instance.n_pigeons);
            n_pigeon_axioms + ((new_h - 1) as usize) * p_choose_2 + new_local
        }
    };

    // Unknown orbits: (axiom_idx, multiplier_monomial).
    let mut unknown_orbits: Vec<Vec<(usize, Monomial)>> = Vec::new();
    let mut pair_to_orbit: BTreeMap<(usize, Monomial), usize> = BTreeMap::new();

    for (i, deg_i) in axiom_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        let mus = enumerate_monomials_up_to(n, budget);
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
                for (sigma, tau) in &gens {
                    let ni = apply_axiom(ci, sigma, tau);
                    let nmu = instance.apply_mono(&cmu, sigma, tau);
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

    // Build matrix over 𝔽_p. Rows are monomial orbits, columns are unknown
    // orbits. entry[R][C] = coefficient of any M ∈ R in
    // ∑_{(i, μ) ∈ C} μ · axioms[i], mod p. This is well-defined by
    // G-equivariance; we pick M as the orbit representative.
    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, members) in unknown_orbits.iter().enumerate() {
        // Accumulate ∑_{(i, μ) ∈ members} μ · axioms[i] at its monomial
        // decomposition, then fold coefficients onto monomial-orbit rows.
        let mut accum_poly = PolyP::zero(p);
        for (ai, mu) in members {
            let mu_poly = PolyP::single(p, mu.clone(), 1);
            let contrib = mu_poly.mul(&axioms[*ai]);
            accum_poly.add_assign(&contrib);
        }
        // Project onto orbit rows: for each monomial M in accum_poly,
        // find M's orbit row and XOR-with-coef the matrix entry. But we
        // want G-invariant per-orbit: a monomial M in the accumulator
        // contributes the SAME coefficient as any other monomial in its
        // orbit (the accumulator IS G-invariant since the unknown orbit
        // is the full orbit under G). So we just read the coefficient at
        // the orbit representative.
        for (m, c) in &accum_poly.terms {
            if let Some(&idx) = mono_index.get(m) {
                let row = mono_orbit_id[idx];
                // Only add once per orbit: check if m is the orbit rep,
                // else skip (other members of the orbit will contribute
                // the same coefficient, already counted).
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
    let mod_inv = |a: u8, p: u8| -> u8 {
        for k in 1..p {
            if (a as u16 * k as u16) % p as u16 == 1 {
                return k;
            }
        }
        panic!("no inverse of {} mod {}", a, p);
    };

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
        let all_zero_lhs = matrix[r][..n_cols].iter().all(|&v| v == 0);
        if all_zero_lhs && matrix[r][n_cols] != 0 {
            return None;
        }
    }

    // Extract solution.
    let mut solution = vec![0u8; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            solution[col] = matrix[*pivot_row][n_cols];
        }
    }

    // Reconstruct full (non-orbit-reduced) cert from orbit solution.
    // For selected orbit with coefficient c, every (i, μ) in the orbit
    // contributes coefficient c to the multiplier of axiom i at monomial μ.
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
    use crate::algebra::ns::verify_certificate;

    #[test]
    fn pair_index_roundtrip() {
        let p = 5;
        for p1 in 1..p {
            for p2 in (p1 + 1)..=p {
                let i = pair_to_pair_index(p1, p2, p);
                let (q1, q2) = pair_index_to_pair(i, p);
                assert_eq!((p1, p2), (q1, q2), "roundtrip at ({}, {})", p1, p2);
            }
        }
    }

    /// Empirical finding: PHP over 𝔽₂ has NO G-INVARIANT NS cert at low
    /// degrees. This matches the theoretical prediction: |G| = P! · H! is
    /// even, so symmetrizing an 𝔽₂ cert gives the zero certificate. The
    /// genuine PHP cert over 𝔽₂ (found by naive NS at degree ~2n) is
    /// non-G-invariant.
    ///
    /// This test documents the negative result. Pivot: NS over 𝔽_p for
    /// odd p — see `ns_fp.rs`.
    #[test]
    fn php_3_2_has_no_g_invariant_f2_cert_at_low_degree() {
        let php = Php::new(3, 2);
        for d in 2..=5 {
            match find_php_orbit_cert(&php, d) {
                NsResult::Unsat(_) => {
                    panic!("unexpected: orbit cert found at d={} — re-examine theory", d);
                }
                NsResult::NoCertificate => {
                    eprintln!("PHP_{{3,2}} orbit/𝔽₂: no G-invariant cert at d={}", d);
                }
            }
        }
    }

    /// Dense (non-orbit) 𝔽₇ baseline for PHP_{5,4} to establish expected
    /// degree before comparing to orbit reduction.
    #[test]
    fn php_5_4_dense_f7_baseline() {
        use crate::algebra::ns_fp::{find_ns_p_from_axioms, php_functional_axioms};
        let axioms = php_functional_axioms(5, 4, 7);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, 20, d, 7) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{5,4}} dense 𝔽₇ d={}: CERT ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{5,4}} dense 𝔽₇ d={}: no cert ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    /// Orbit-reduced NS over 𝔽_p: PHP_{5,4} with p=7 (7 ∤ 5!·4!).
    /// Compare with dense 𝔽₃ result (d=3, 60ms).
    #[test]
    fn php_5_4_functional_orbit_f7() {
        let php = Php::new(5, 4);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_php_functional_orbit_cert_fp(&php, d, 7) {
                Some(mults) => {
                    eprintln!(
                        "PHP_{{5,4}} orbit 𝔽₇ d={}: CERT, {} axioms used ({:.3}s)",
                        d,
                        mults.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{5,4}} orbit 𝔽₇ d={}: no cert ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
        panic!("PHP_{{5,4}} must have orbit-invariant cert at d≤5 over 𝔽₇");
    }

    /// Orbit-reduced NS over 𝔽_p: PHP_{6,5}. Dense 𝔽₅ failed at d=4 in 335s.
    /// Orbit 𝔽_p should find a cert in milliseconds.
    #[test]
    fn php_6_5_functional_orbit_f7() {
        let php = Php::new(6, 5);
        for d in 2..=6 {
            let t = std::time::Instant::now();
            match find_php_functional_orbit_cert_fp(&php, d, 7) {
                Some(mults) => {
                    eprintln!(
                        "PHP_{{6,5}} orbit 𝔽₇ d={}: CERT, {} axioms ({:.3}s)",
                        d,
                        mults.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{6,5}} orbit 𝔽₇ d={}: no cert ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    /// The target: PHP_{10,9} via orbit-reduced 𝔽_{11}. Monomial count
    /// collapses from ~121k to ~10 orbits.
    #[test]
    #[ignore] // gated behind --ignored; this IS the headline benchmark
    fn php_10_9_functional_orbit_f11() {
        let php = Php::new(10, 9);
        for d in 2..=4 {
            let t = std::time::Instant::now();
            match find_php_functional_orbit_cert_fp(&php, d, 11) {
                Some(mults) => {
                    eprintln!(
                        "PHP_{{10,9}} orbit 𝔽₁₁ d={}: CERT, {} axioms ({:.3}s)",
                        d,
                        mults.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{10,9}} orbit 𝔽₁₁ d={}: no cert ({:.3}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    fn php_4_3_orbit_probe() {
        let php = Php::new(4, 3);
        let t = std::time::Instant::now();
        let mut found = None;
        for d in 3..=7 {
            let t_d = std::time::Instant::now();
            match find_php_orbit_cert(&php, d) {
                NsResult::Unsat(cert) => {
                    let clauses = php.clauses();
                    let valid = verify_certificate(&cert, &clauses);
                    eprintln!(
                        "PHP_{{4,3}} orbit d={}: cert={} terms, {:.2}s, verify={}",
                        d,
                        cert.terms.len(),
                        t_d.elapsed().as_secs_f64(),
                        valid
                    );
                    if valid {
                        found = Some(d);
                        break;
                    }
                }
                NsResult::NoCertificate => {
                    eprintln!(
                        "PHP_{{4,3}} orbit d={}: no cert ({:.2}s)",
                        d,
                        t_d.elapsed().as_secs_f64()
                    );
                }
            }
        }
        eprintln!("PHP_{{4,3}} total: {:.2}s", t.elapsed().as_secs_f64());
        // Don't assert — this is a probe.
    }
}
