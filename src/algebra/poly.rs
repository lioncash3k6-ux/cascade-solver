//! Multilinear polynomials over 𝔽₂.
//!
//! In 𝔽₂[x₁,…,xₙ]/(x² - x, for each x), every polynomial is
//! equivalent to a multilinear one (no variable ever appears squared
//! or higher). Coefficients are in {0, 1}. We represent a polynomial
//! as the set of monomials with coefficient 1.
//!
//! Operations:
//! * add = symmetric difference (xor) of monomial sets.
//! * mul = outer product with `x² → x` reduction.
//! * eval at a 0/1 assignment.

use std::collections::BTreeSet;
use std::fmt;

/// 𝔽₂ scalar — mostly used as a type tag.
#[derive(Copy, Clone, PartialEq, Eq)]
pub struct F2(pub bool);

impl fmt::Debug for F2 {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0 as u8)
    }
}

/// A multilinear monomial: the set of variables in its support. Ordered
/// (BTreeSet) so monomials are canonical and comparable. Variables are
/// u32 (DIMACS-style, 1-indexed).
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct Monomial(pub BTreeSet<u32>);

impl Monomial {
    pub fn one() -> Self {
        Monomial(BTreeSet::new())
    }

    pub fn single(v: u32) -> Self {
        let mut s = BTreeSet::new();
        s.insert(v);
        Monomial(s)
    }

    pub fn from_vars<I: IntoIterator<Item = u32>>(vars: I) -> Self {
        Monomial(vars.into_iter().collect())
    }

    pub fn degree(&self) -> usize {
        self.0.len()
    }

    pub fn is_one(&self) -> bool {
        self.0.is_empty()
    }

    /// Multilinear multiplication: `x · x = x`, so set-union handles
    /// reduction automatically.
    pub fn mul(&self, other: &Self) -> Self {
        let mut s = self.0.clone();
        for &v in &other.0 {
            s.insert(v);
        }
        Monomial(s)
    }

    /// Evaluate under an assignment (`assign[v]` is bool, 1-indexed;
    /// `assign[0]` is padding). Unmentioned vars must be concrete.
    pub fn eval(&self, assign: &[bool]) -> bool {
        for &v in &self.0 {
            if !assign[v as usize] {
                return false;
            }
        }
        true
    }

    pub fn vars(&self) -> impl Iterator<Item = u32> + '_ {
        self.0.iter().copied()
    }
}

impl fmt::Debug for Monomial {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "1");
        }
        let mut first = true;
        for &v in &self.0 {
            if first {
                write!(f, "x{}", v)?;
                first = false;
            } else {
                write!(f, "·x{}", v)?;
            }
        }
        Ok(())
    }
}

/// A multilinear polynomial over 𝔽₂: the set of monomials with
/// coefficient 1. Empty set = the zero polynomial. `{one()}` = the
/// constant 1.
#[derive(Clone, PartialEq, Eq, Default)]
pub struct Poly(pub BTreeSet<Monomial>);

impl Poly {
    pub fn zero() -> Self {
        Poly(BTreeSet::new())
    }

    pub fn one() -> Self {
        let mut s = BTreeSet::new();
        s.insert(Monomial::one());
        Poly(s)
    }

    /// `x_v` as a polynomial (one monomial of degree 1).
    pub fn var(v: u32) -> Self {
        let mut s = BTreeSet::new();
        s.insert(Monomial::single(v));
        Poly(s)
    }

    /// `1 - x_v` as a polynomial. Over 𝔽₂, `1 - x = 1 + x`.
    pub fn not_var(v: u32) -> Self {
        let mut s = BTreeSet::new();
        s.insert(Monomial::one());
        s.insert(Monomial::single(v));
        Poly(s)
    }

    /// Build polynomial from a DIMACS literal: `l = +v` → `x_v`;
    /// `l = -v` → `1 + x_v`.
    pub fn from_lit(l: i32) -> Self {
        let v = l.unsigned_abs();
        if l > 0 {
            Self::var(v)
        } else {
            Self::not_var(v)
        }
    }

    pub fn is_zero(&self) -> bool {
        self.0.is_empty()
    }

    pub fn is_one(&self) -> bool {
        self.0.len() == 1 && self.0.iter().next().unwrap().is_one()
    }

    /// Addition over 𝔽₂ is symmetric difference.
    pub fn add(&self, other: &Self) -> Self {
        let mut out = self.0.clone();
        for m in &other.0 {
            if !out.remove(m) {
                out.insert(m.clone());
            }
        }
        Poly(out)
    }

    /// In-place add.
    pub fn add_assign(&mut self, other: &Self) {
        for m in &other.0 {
            if !self.0.remove(m) {
                self.0.insert(m.clone());
            }
        }
    }

    /// Multiplication: outer product of monomial sets, with 𝔽₂
    /// accumulation via symmetric difference.
    pub fn mul(&self, other: &Self) -> Self {
        let mut out = BTreeSet::<Monomial>::new();
        for a in &self.0 {
            for b in &other.0 {
                let m = a.mul(b);
                if !out.remove(&m) {
                    out.insert(m);
                }
            }
        }
        Poly(out)
    }

    /// Maximum degree of any monomial (returns 0 for zero polynomial
    /// and for the constant-1 polynomial).
    pub fn degree(&self) -> usize {
        self.0.iter().map(|m| m.degree()).max().unwrap_or(0)
    }

    /// Evaluate under an assignment.
    pub fn eval(&self, assign: &[bool]) -> bool {
        let mut acc = false;
        for m in &self.0 {
            if m.eval(assign) {
                acc = !acc;
            }
        }
        acc
    }

    /// Product of polynomials in a slice (left-fold; 1 for empty).
    pub fn product(factors: &[Poly]) -> Self {
        let mut p = Self::one();
        for f in factors {
            p = p.mul(f);
        }
        p
    }

    /// The clause polynomial: a DIMACS clause `(l_1 ∨ … ∨ l_k)` is
    /// False iff `∏ (1 - l̃_i) = 1`. We emit `∏ (1 - l̃_i)`, which
    /// should reduce to 0 under the ideal of F.
    pub fn clause_poly(clause: &[i32]) -> Self {
        let factors: Vec<Poly> = clause
            .iter()
            .map(|&l| {
                // "1 - lit_value" where lit_value = x_v if l>0, 1-x_v if l<0.
                // If l > 0: 1 - x_v = not_var(v).
                // If l < 0: 1 - (1 - x_v) = x_v.
                if l > 0 {
                    Poly::not_var(l.unsigned_abs())
                } else {
                    Poly::var(l.unsigned_abs())
                }
            })
            .collect();
        Self::product(&factors)
    }
}

impl fmt::Debug for Poly {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if self.0.is_empty() {
            return write!(f, "0");
        }
        let mut first = true;
        for m in &self.0 {
            if !first {
                write!(f, " + ")?;
            }
            first = false;
            write!(f, "{:?}", m)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn assign(vals: &[(u32, bool)]) -> Vec<bool> {
        let n = vals.iter().map(|&(v, _)| v).max().unwrap_or(0);
        let mut a = vec![false; n as usize + 1];
        for &(v, b) in vals {
            a[v as usize] = b;
        }
        a
    }

    #[test]
    fn monomial_one_is_empty() {
        assert!(Monomial::one().is_one());
        assert_eq!(Monomial::one().degree(), 0);
    }

    #[test]
    fn monomial_multiplication_is_set_union() {
        let a = Monomial::from_vars([1, 2, 3]);
        let b = Monomial::from_vars([2, 3, 4]);
        let ab = a.mul(&b);
        let expected = Monomial::from_vars([1, 2, 3, 4]);
        assert_eq!(ab, expected);
    }

    #[test]
    fn poly_add_is_symmetric_difference() {
        let p = Poly::var(1).add(&Poly::var(2));
        let q = Poly::var(2).add(&Poly::var(3));
        let s = p.add(&q); // x1 + x3 (x2 cancels)
        let expected = Poly::var(1).add(&Poly::var(3));
        assert_eq!(s, expected);
    }

    #[test]
    fn poly_x_plus_x_is_zero() {
        let p = Poly::var(1).add(&Poly::var(1));
        assert!(p.is_zero());
    }

    #[test]
    fn poly_one_times_anything_is_anything() {
        let q = Poly::var(1).add(&Poly::not_var(2));
        let p = Poly::one().mul(&q);
        assert_eq!(p, q);
    }

    #[test]
    fn poly_zero_times_anything_is_zero() {
        let q = Poly::var(1).add(&Poly::not_var(2));
        let p = Poly::zero().mul(&q);
        assert!(p.is_zero());
    }

    #[test]
    fn poly_x_times_x_is_x() {
        // In 𝔽₂[x]/(x² - x), x · x = x.
        let p = Poly::var(1).mul(&Poly::var(1));
        assert_eq!(p, Poly::var(1));
    }

    #[test]
    fn poly_1_minus_x_times_x_is_zero() {
        // (1 + x) · x = x + x² = x + x = 0 in 𝔽₂[x]/(x² - x).
        let p = Poly::not_var(1).mul(&Poly::var(1));
        assert!(p.is_zero());
    }

    #[test]
    fn clause_poly_disjunction_falsified_iff_all_false() {
        // Clause (x1 ∨ x2). Poly = (1-x1)(1-x2) = 1 + x1 + x2 + x1 x2.
        let c = Poly::clause_poly(&[1, 2]);
        assert_eq!(c.eval(&assign(&[(1, false), (2, false)])), true);
        assert_eq!(c.eval(&assign(&[(1, true), (2, false)])), false);
        assert_eq!(c.eval(&assign(&[(1, false), (2, true)])), false);
        assert_eq!(c.eval(&assign(&[(1, true), (2, true)])), false);
    }

    #[test]
    fn clause_poly_mixed_polarity() {
        // Clause (x1 ∨ ¬x2). Poly = (1 - x1)(1 - (1-x2)) = (1+x1)·x2 = x2 + x1·x2.
        let c = Poly::clause_poly(&[1, -2]);
        // False iff x1=0 AND x2=1.
        assert_eq!(c.eval(&assign(&[(1, false), (2, true)])), true);
        assert_eq!(c.eval(&assign(&[(1, true), (2, true)])), false);
        assert_eq!(c.eval(&assign(&[(1, false), (2, false)])), false);
    }

    #[test]
    fn poly_degree_tracks_max_monomial() {
        let p = Poly::var(1).add(&Poly::var(2).mul(&Poly::var(3)));
        assert_eq!(p.degree(), 2);
    }

    #[test]
    fn poly_zero_has_degree_zero() {
        assert_eq!(Poly::zero().degree(), 0);
    }
}
