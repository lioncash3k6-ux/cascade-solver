//! Core SAT types: Var, Lit, Clause, ClauseId.
//!
//! Var is 1-indexed (matches DIMACS).
//! Lit is i32 with sign indicating polarity (positive = positive lit, negative = negated).
//! Lit 0 is the DIMACS clause terminator and is never a valid literal.

use std::fmt;

/// A SAT variable, 1-indexed (1..=nvars). Var(0) is invalid.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Var(pub u32);

impl Var {
    pub const INVALID: Var = Var(0);

    #[inline]
    pub fn new(v: u32) -> Self {
        debug_assert!(v != 0, "Var(0) is invalid");
        Var(v)
    }

    #[inline]
    pub fn as_index(self) -> usize {
        self.0 as usize
    }

    #[inline]
    pub fn pos(self) -> Lit {
        Lit(self.0 as i32)
    }

    #[inline]
    pub fn neg(self) -> Lit {
        Lit(-(self.0 as i32))
    }
}

impl fmt::Debug for Var {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "v{}", self.0)
    }
}

/// A SAT literal. Stored as a signed integer matching DIMACS convention.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct Lit(pub i32);

impl Lit {
    pub const ZERO: Lit = Lit(0);

    #[inline]
    pub fn new(raw: i32) -> Self {
        debug_assert!(raw != 0, "Lit(0) is invalid");
        Lit(raw)
    }

    #[inline]
    pub fn var(self) -> Var {
        Var(self.0.unsigned_abs())
    }

    #[inline]
    pub fn is_positive(self) -> bool {
        self.0 > 0
    }

    #[inline]
    pub fn is_negative(self) -> bool {
        self.0 < 0
    }

    #[inline]
    pub fn negate(self) -> Lit {
        Lit(-self.0)
    }

    #[inline]
    pub fn raw(self) -> i32 {
        self.0
    }
}

impl fmt::Debug for Lit {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl From<i32> for Lit {
    fn from(raw: i32) -> Lit {
        Lit::new(raw)
    }
}

/// A clause identifier (1-indexed for compatibility with LRAT).
/// IDs are stable across the proof file: input clauses get 1..=nclauses,
/// derived clauses get larger IDs assigned sequentially.
#[derive(Copy, Clone, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub struct ClauseId(pub u64);

impl ClauseId {
    pub const INVALID: ClauseId = ClauseId(0);

    #[inline]
    pub fn new(id: u64) -> Self {
        debug_assert!(id != 0, "ClauseId(0) is invalid");
        ClauseId(id)
    }

    #[inline]
    pub fn raw(self) -> u64 {
        self.0
    }
}

impl fmt::Debug for ClauseId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "c{}", self.0)
    }
}

/// A SAT clause. Owns its literals as a Vec for now (can move to arena later).
#[derive(Clone, Debug)]
pub struct Clause {
    lits: Vec<Lit>,
}

impl Clause {
    pub fn new(lits: Vec<Lit>) -> Self {
        Clause { lits }
    }

    pub fn empty() -> Self {
        Clause { lits: Vec::new() }
    }

    #[inline]
    pub fn lits(&self) -> &[Lit] {
        &self.lits
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.lits.len()
    }

    #[inline]
    pub fn is_empty(&self) -> bool {
        self.lits.is_empty()
    }

    #[inline]
    pub fn is_unit(&self) -> bool {
        self.lits.len() == 1
    }

    /// Sort literals by absolute value (canonical form).
    pub fn sort(&mut self) {
        self.lits.sort_by_key(|l| (l.var().0, l.0));
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lit_negation() {
        assert_eq!(Lit::new(1).negate(), Lit::new(-1));
        assert_eq!(Lit::new(-5).negate(), Lit::new(5));
        assert_eq!(Lit::new(-5).var(), Var::new(5));
    }

    #[test]
    fn var_to_lit() {
        let v = Var::new(7);
        assert_eq!(v.pos(), Lit::new(7));
        assert_eq!(v.neg(), Lit::new(-7));
    }

    #[test]
    fn clause_basics() {
        let c = Clause::new(vec![Lit::new(1), Lit::new(-3), Lit::new(5)]);
        assert_eq!(c.len(), 3);
        assert!(!c.is_empty());
        assert!(!c.is_unit());

        let e = Clause::empty();
        assert!(e.is_empty());

        let u = Clause::new(vec![Lit::new(2)]);
        assert!(u.is_unit());
    }
}
