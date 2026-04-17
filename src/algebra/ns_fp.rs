//! Nullstellensatz over 𝔽_p for odd prime p.
//!
//! Generalizes `ns.rs` (which is 𝔽₂-specific, bit-packed) to arbitrary
//! small prime moduli. The motivating instance: PHP_{P,H} has NS degree
//! Θ(n) over 𝔽₂ (hard) but Θ(log n) over 𝔽_p for many p ∤ P (easy —
//! classical counting argument).
//!
//! # Representation
//!
//! * Polynomials: `BTreeMap<Monomial, u8>` where `u8 ∈ {1, ..., p-1}`
//!   (zero coefficients omitted).
//! * Multilinear quotient: x² = x in any field (since Boolean vars).
//! * Clause polynomial: same construction, with `−1 ≡ p−1 mod p`.
//!
//! # Matrix
//!
//! Dense `Vec<Vec<u8>>`. For moderately small instances this is fine;
//! a sparse representation is a later optimization.

use super::ns::{CertTerm, NsCertificate, NsResult};
use super::poly::Monomial;
use std::collections::BTreeMap;

/// Polynomial over 𝔽_p.
#[derive(Clone, Debug)]
pub struct PolyP {
    pub p: u8,
    pub terms: BTreeMap<Monomial, u8>,
}

impl PolyP {
    pub fn zero(p: u8) -> Self {
        Self {
            p,
            terms: BTreeMap::new(),
        }
    }

    pub fn one(p: u8) -> Self {
        let mut t = BTreeMap::new();
        t.insert(Monomial::one(), 1);
        Self { p, terms: t }
    }

    pub fn single(p: u8, m: Monomial, c: u8) -> Self {
        let c = c % p;
        let mut t = BTreeMap::new();
        if c != 0 {
            t.insert(m, c);
        }
        Self { p, terms: t }
    }

    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    pub fn is_one(&self) -> bool {
        self.terms.len() == 1 && self.terms.get(&Monomial::one()) == Some(&1)
    }

    pub fn degree(&self) -> usize {
        self.terms.keys().map(|m| m.degree()).max().unwrap_or(0)
    }

    pub fn add_assign(&mut self, other: &Self) {
        debug_assert_eq!(self.p, other.p);
        for (m, c) in &other.terms {
            let e = self.terms.entry(m.clone()).or_insert(0);
            *e = (*e + c) % self.p;
            if *e == 0 {
                self.terms.remove(m);
            }
        }
    }

    pub fn mul(&self, other: &Self) -> Self {
        debug_assert_eq!(self.p, other.p);
        let mut out: BTreeMap<Monomial, u8> = BTreeMap::new();
        for (ma, ca) in &self.terms {
            for (mb, cb) in &other.terms {
                let m = ma.mul(mb);
                let c = ((*ca as u16 * *cb as u16) % self.p as u16) as u8;
                if c == 0 {
                    continue;
                }
                let e = out.entry(m).or_insert(0);
                *e = (*e + c) % self.p;
            }
        }
        out.retain(|_, v| *v != 0);
        Self { p: self.p, terms: out }
    }

    /// Clause polynomial: ∏ (1 - lit_value_i). `1 - x_v = 1 + (p-1)·x_v`;
    /// `1 - (1 - x_v) = x_v`.
    pub fn clause_poly(p: u8, clause: &[i32]) -> Self {
        let mut acc = Self::one(p);
        for &l in clause {
            let mut fac = BTreeMap::new();
            let v = l.unsigned_abs();
            if l > 0 {
                fac.insert(Monomial::one(), 1u8);
                fac.insert(Monomial::single(v), p - 1);
            } else {
                fac.insert(Monomial::single(v), 1u8);
            }
            let f = Self { p, terms: fac };
            acc = acc.mul(&f);
        }
        acc
    }
}

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

/// Modular inverse of `a` mod `p`. Panics if `a ≡ 0` or `p` not prime.
fn mod_inv(a: u8, p: u8) -> u8 {
    // p is small; brute-force.
    for k in 1..p {
        if (a as u16 * k as u16) % p as u16 == 1 {
            return k;
        }
    }
    panic!("no inverse of {} mod {}", a, p);
}

/// Find a degree-`d` NS certificate for `F = clauses` over 𝔽_p.
pub fn find_ns_p_certificate(
    clauses: &[Vec<i32>],
    n: u32,
    d: usize,
    p: u8,
) -> NsResult {
    assert!(p >= 2 && p <= 251, "unsupported prime {}", p);
    if clauses.is_empty() {
        return NsResult::NoCertificate;
    }

    let clause_polys: Vec<PolyP> = clauses
        .iter()
        .map(|c| PolyP::clause_poly(p, c))
        .collect();
    let clause_degrees: Vec<usize> = clause_polys.iter().map(|q| q.degree()).collect();
    let monomials = enumerate_monomials_up_to(n, d);
    let mono_index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();

    // Unknowns: (clause_idx, multiplier_monomial).
    let mut unknowns: Vec<(usize, Monomial)> = Vec::new();
    for (i, deg_i) in clause_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        for mu in enumerate_monomials_up_to(n, budget) {
            unknowns.push((i, mu));
        }
    }
    if unknowns.is_empty() {
        return NsResult::NoCertificate;
    }

    let n_rows = monomials.len();
    let n_cols = unknowns.len();
    // Dense matrix of u8; last column = RHS.
    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, (ci, mu)) in unknowns.iter().enumerate() {
        // μ · P_i expanded.
        let mu_poly = PolyP::single(p, mu.clone(), 1);
        let prod = mu_poly.mul(&clause_polys[*ci]);
        for (m, c) in &prod.terms {
            if let Some(&row) = mono_index.get(m) {
                matrix[row][col] = (matrix[row][col] + *c) % p;
            }
        }
    }
    let one_row = *mono_index.get(&Monomial::one()).expect("empty monomial row");
    matrix[one_row][n_cols] = 1;

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
            Some(p_row) => p_row,
            None => continue,
        };
        matrix.swap(pivot, row);
        // Scale pivot row so pivot entry = 1.
        let a = matrix[row][col];
        if a != 1 {
            let inv = mod_inv(a, p);
            for v in &mut matrix[row] {
                *v = ((*v as u16 * inv as u16) % p as u16) as u8;
            }
        }
        pivot_row_of_col[col] = Some(row);
        // Eliminate in other rows.
        for r in 0..n_rows {
            if r == row {
                continue;
            }
            let k = matrix[r][col];
            if k == 0 {
                continue;
            }
            // row r -= k * row.
            // We need: matrix[r] = matrix[r] - k * matrix[row] (mod p).
            //        = matrix[r] + (p - k) * matrix[row].
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
            return NsResult::NoCertificate;
        }
    }

    // Extract: free vars = 0. Pivot var = RHS of pivot row.
    let mut solution = vec![0u8; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            solution[col] = matrix[*pivot_row][n_cols];
        }
    }

    // Convert back to certificate. The NS cert in our API uses 𝔽₂ Poly;
    // for 𝔽_p we need to emit a PolyP per clause. Since NsCertificate holds
    // `Poly` (𝔽₂), we emit a *different* summary here.
    //
    // For now: return a "virtual" cert whose terms contain all nonzero
    // multipliers as Poly where we forget the coefficient and keep support
    // only — adequate for degree reporting but NOT verifiable via 𝔽₂
    // verify_certificate. A real 𝔽_p verifier lives below.
    //
    // Instead, pack the 𝔽_p cert in a parallel type.
    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        let (ci, mu) = &unknowns[col];
        let entry = mults.entry(*ci).or_insert_with(|| PolyP::zero(p));
        let term = PolyP::single(p, mu.clone(), coef);
        entry.add_assign(&term);
    }
    let valid = verify_cert_p(&mults, clauses, p);
    if !valid {
        return NsResult::NoCertificate;
    }

    // Return an NS result with term COUNT but no Poly contents (since Poly
    // is 𝔽₂). Degree is recorded. Caller can verify via `verify_cert_p`
    // given a PolyP map, but find_ns_p returns the Poly-based struct for
    // uniformity. We encode each coefficient's monomial into Poly for
    // reporting; numerical coefficient is lost here.
    let terms: Vec<CertTerm> = mults
        .iter()
        .filter(|(_, q)| !q.is_zero())
        .map(|(&clause_idx, q)| {
            // Store monomial support only, for reporting.
            let mut support = super::poly::Poly::zero();
            for m in q.terms.keys() {
                support.add_assign(&{
                    let mut s = std::collections::BTreeSet::new();
                    s.insert(m.clone());
                    super::poly::Poly(s)
                });
            }
            CertTerm {
                clause_idx,
                multiplier: support,
            }
        })
        .collect();

    if terms.is_empty() {
        return NsResult::NoCertificate;
    }
    NsResult::Unsat(NsCertificate { degree: d, terms })
}

/// Verify a 𝔽_p certificate represented as clause_idx → PolyP multiplier.
pub fn verify_cert_p(
    mults: &BTreeMap<usize, PolyP>,
    clauses: &[Vec<i32>],
    p: u8,
) -> bool {
    let mut acc = PolyP::zero(p);
    for (&ci, mult) in mults {
        let cp = PolyP::clause_poly(p, &clauses[ci]);
        let contrib = mult.mul(&cp);
        acc.add_assign(&contrib);
    }
    acc.is_one()
}

/// Find a degree-`d` NS certificate over 𝔽_p for a formula given as
/// polynomial axioms (each vanishing on the model set). Unlike
/// [`find_ns_p_certificate`], this accepts arbitrary axioms (not just
/// CNF clauses) — the classical way to encode functional PHP as linear
/// equations `∑_h x(p,h) - 1 = 0`.
///
/// Returns (degree, axiom_idx → multiplier) on success.
pub fn find_ns_p_from_axioms(
    axioms: &[PolyP],
    n: u32,
    d: usize,
    p: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    assert!(p >= 2 && p <= 251);
    if axioms.is_empty() {
        return None;
    }

    let axiom_degrees: Vec<usize> = axioms.iter().map(|a| a.degree()).collect();
    let monomials = enumerate_monomials_up_to(n, d);
    let mono_index: BTreeMap<Monomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(i, m)| (m, i))
        .collect();

    let mut unknowns: Vec<(usize, Monomial)> = Vec::new();
    for (i, deg_i) in axiom_degrees.iter().enumerate() {
        if *deg_i > d {
            continue;
        }
        let budget = d - deg_i;
        for mu in enumerate_monomials_up_to(n, budget) {
            unknowns.push((i, mu));
        }
    }
    if unknowns.is_empty() {
        return None;
    }

    let n_rows = monomials.len();
    let n_cols = unknowns.len();
    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, (ai, mu)) in unknowns.iter().enumerate() {
        let mu_poly = PolyP::single(p, mu.clone(), 1);
        let prod = mu_poly.mul(&axioms[*ai]);
        for (m, c) in &prod.terms {
            if let Some(&row) = mono_index.get(m) {
                matrix[row][col] = (matrix[row][col] + *c) % p;
            }
        }
    }
    let one_row = *mono_index.get(&Monomial::one()).expect("empty monomial row");
    matrix[one_row][n_cols] = 1;

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
            Some(p_row) => p_row,
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

    for r in 0..n_rows {
        let all_zero_lhs = matrix[r][..n_cols].iter().all(|&v| v == 0);
        if all_zero_lhs && matrix[r][n_cols] != 0 {
            return None;
        }
    }

    let mut solution = vec![0u8; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            solution[col] = matrix[*pivot_row][n_cols];
        }
    }

    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        let (ai, mu) = &unknowns[col];
        let entry = mults.entry(*ai).or_insert_with(|| PolyP::zero(p));
        let term = PolyP::single(p, mu.clone(), coef);
        entry.add_assign(&term);
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

/// Build functional PHP axioms as polynomials over 𝔽_p:
/// * Pigeon totality (linear, degree 1): ∑_h x(p,h) - 1 = 0 for each p.
/// * AMO per hole (degree 2): x(p1,h) · x(p2,h) = 0 for each (h, p1<p2).
pub fn php_functional_axioms(n_pigeons: u32, n_holes: u32, p: u8) -> Vec<PolyP> {
    let var = |pp: u32, hh: u32| -> u32 { (pp - 1) * n_holes + hh };
    let mut out = Vec::new();
    // Totality: ∑_h x(p,h) - 1.
    for pp in 1..=n_pigeons {
        let mut terms = BTreeMap::new();
        for hh in 1..=n_holes {
            terms.insert(Monomial::single(var(pp, hh)), 1u8);
        }
        terms.insert(Monomial::one(), p - 1); // -1 mod p.
        out.push(PolyP { p, terms });
    }
    // AMO: x(p1,h) · x(p2,h).
    for hh in 1..=n_holes {
        for p1 in 1..=n_pigeons {
            for p2 in (p1 + 1)..=n_pigeons {
                let m = Monomial::from_vars([var(p1, hh), var(p2, hh)]);
                let mut terms = BTreeMap::new();
                terms.insert(m, 1u8);
                out.push(PolyP { p, terms });
            }
        }
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn trivial_unsat_over_f3() {
        let clauses = vec![vec![1], vec![-1]];
        match find_ns_p_certificate(&clauses, 1, 1, 3) {
            NsResult::Unsat(_) => {}
            _ => panic!("expected cert at d=1 over 𝔽₃"),
        }
    }

    #[test]
    fn sat_has_no_cert_over_f3() {
        let clauses = vec![vec![1, 2]];
        for d in 1..=3 {
            match find_ns_p_certificate(&clauses, 2, d, 3) {
                NsResult::Unsat(_) => panic!("spurious cert at d={}", d),
                NsResult::NoCertificate => {}
            }
        }
    }

    #[test]
    fn triangle_unsat_over_f3() {
        // x1 ∧ x2 ∧ ¬x1∨¬x2.
        let clauses = vec![vec![1], vec![2], vec![-1, -2]];
        match find_ns_p_certificate(&clauses, 2, 2, 3) {
            NsResult::Unsat(_) => {}
            _ => panic!("expected degree-2 cert over 𝔽₃"),
        }
    }

    /// PHP_{3,2} over 𝔽₃: does a low-degree cert exist?
    /// Over 𝔽₂ the cert is degree 4. We want to see if 𝔽₃ gives a smaller
    /// degree (theory says: if P=3 is not divisible by char=3, counting
    /// cert at degree O(log H) = O(1) exists. But 3 | 3, so 𝔽₃ fails for
    /// P=3. Expect no low-degree cert; use 𝔽₅ instead.)
    #[test]
    fn php_3_2_over_f3() {
        use crate::algebra::php_orbit::Php;
        let php = Php::new(3, 2);
        let clauses = php.clauses();
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_certificate(&clauses, php.n_vars(), d, 3) {
                NsResult::Unsat(cert) => {
                    eprintln!(
                        "PHP_{{3,2}} 𝔽₃ d={}: cert with {} terms ({:.2}s)",
                        d,
                        cert.terms.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                NsResult::NoCertificate => {
                    eprintln!(
                        "PHP_{{3,2}} 𝔽₃ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    fn php_3_2_over_f5() {
        use crate::algebra::php_orbit::Php;
        let php = Php::new(3, 2);
        let clauses = php.clauses();
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_certificate(&clauses, php.n_vars(), d, 5) {
                NsResult::Unsat(cert) => {
                    eprintln!(
                        "PHP_{{3,2}} 𝔽₅ d={}: cert with {} terms ({:.2}s)",
                        d,
                        cert.terms.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                NsResult::NoCertificate => {
                    eprintln!(
                        "PHP_{{3,2}} 𝔽₅ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore] // multi-second runtime at d≥6; opt-in only
    fn php_4_3_over_f3_probe() {
        use crate::algebra::php_orbit::Php;
        let php = Php::new(4, 3);
        let clauses = php.clauses();
        for d in 2..=7 {
            let t = std::time::Instant::now();
            match find_ns_p_certificate(&clauses, php.n_vars(), d, 3) {
                NsResult::Unsat(cert) => {
                    eprintln!(
                        "PHP_{{4,3}} 𝔽₃ d={}: cert with {} terms ({:.2}s)",
                        d,
                        cert.terms.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                NsResult::NoCertificate => {
                    eprintln!(
                        "PHP_{{4,3}} 𝔽₃ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    /// Functional PHP over 𝔽_p: the theoretically low-degree variant.
    /// Axioms: linear totality ∑_h x(p,h) = 1 per pigeon + quadratic AMO.
    /// Expected: degree O(log H) when gcd(p, P) = 1.
    #[test]
    fn php_4_3_functional_f5() {
        let n_vars = 4 * 3;
        let axioms = php_functional_axioms(4, 3, 5);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 5) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{4,3}} functional 𝔽₅ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{4,3}} functional 𝔽₅ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    fn php_5_4_functional_f3() {
        // P=5, H=4. gcd(3, 5) = 1, so 𝔽₃ works.
        let n_vars = 5 * 4;
        let axioms = php_functional_axioms(5, 4, 3);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 3) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{5,4}} functional 𝔽₃ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{5,4}} functional 𝔽₃ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore] // allocates multi-GB matrices at d≥4; opt-in only
    fn php_6_5_functional_f5() {
        // P=6, H=5. gcd(5, 6) = 1, so 𝔽₅ works.
        let n_vars = 6 * 5;
        let axioms = php_functional_axioms(6, 5, 5);
        for d in 2..=5 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 5) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{6,5}} functional 𝔽₅ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{6,5}} functional 𝔽₅ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore] // allocates multi-GB matrices at d≥4; opt-in only
    fn php_7_6_functional_f5() {
        // P=7, H=6. gcd(5, 7) = 1, so 𝔽₅ works.
        let n_vars = 7 * 6;
        let axioms = php_functional_axioms(7, 6, 5);
        for d in 2..=4 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 5) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{7,6}} functional 𝔽₅ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{7,6}} functional 𝔽₅ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn php_8_7_functional_f5() {
        let n_vars = 8 * 7;
        let axioms = php_functional_axioms(8, 7, 5);
        for d in 2..=4 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 5) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{8,7}} functional 𝔽₅ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{8,7}} functional 𝔽₅ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn php_10_9_functional_f7_probe() {
        // P=10, H=9. gcd(7, 10) = 1.
        let n_vars = 10 * 9;
        let axioms = php_functional_axioms(10, 9, 7);
        for d in 2..=4 {
            let t = std::time::Instant::now();
            match find_ns_p_from_axioms(&axioms, n_vars, d, 7) {
                Some(_) => {
                    eprintln!(
                        "PHP_{{10,9}} functional 𝔽₇ d={}: CERT ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                None => {
                    eprintln!(
                        "PHP_{{10,9}} functional 𝔽₇ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }

    #[test]
    #[ignore]
    fn php_5_4_over_f3_probe() {
        use crate::algebra::php_orbit::Php;
        let php = Php::new(5, 4);
        let clauses = php.clauses();
        for d in 2..=6 {
            let t = std::time::Instant::now();
            match find_ns_p_certificate(&clauses, php.n_vars(), d, 3) {
                NsResult::Unsat(cert) => {
                    eprintln!(
                        "PHP_{{5,4}} 𝔽₃ d={}: cert with {} terms ({:.2}s)",
                        d,
                        cert.terms.len(),
                        t.elapsed().as_secs_f64()
                    );
                    return;
                }
                NsResult::NoCertificate => {
                    eprintln!(
                        "PHP_{{5,4}} 𝔽₃ d={}: no cert ({:.2}s)",
                        d,
                        t.elapsed().as_secs_f64()
                    );
                }
            }
        }
    }
}
