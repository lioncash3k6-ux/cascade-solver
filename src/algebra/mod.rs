//! GAPS leg 4 — Algebraic engine (Nullstellensatz-lite over 𝔽₂).
//!
//! This module is the entry point for polynomial reasoning as a
//! side-channel to CDCL. The thesis: when CDCL hits a width wall
//! (certain combinatorial structures produce unavoidable resolution
//! width), a bounded-degree Nullstellensatz certificate over 𝔽₂ can
//! refute the formula in polynomial time and be Tseitin-encoded back
//! into clauses CDCL can consume.
//!
//! # Submodules
//!
//! * [`poly`] — multilinear monomials over 𝔽₂, efficient polynomial
//!   representation via `BTreeMap<Monomial, ()>` (coefficient implicit
//!   since 𝔽₂ has only 0 and 1).
//! * [`ns`] — Nullstellensatz checker: for a given CNF and degree
//!   bound `d`, find a linear combination of clause polynomials that
//!   reduces to 1 (witness of unsat).
//! * [`tseitin`] — encode polynomial certificates back to CNF.
//!
//! # Design notes
//!
//! * Multilinear only — in 𝔽₂, `x² = x`, so we reduce modulo `x² - x`
//!   for every variable. Polynomials live in 𝔽₂[x₁,…,xₙ]/(x² - x).
//! * `bool` values: in the encoding, `x_i = 1` means the literal is
//!   True. A DIMACS clause `(l_1 ∨ … ∨ l_k)` becomes the polynomial
//!   `(1 - l̃_1)(1 - l̃_2)…(1 - l̃_k) = 0`, where `l̃ = x_i` if `l = +i`
//!   and `l̃ = 1 - x_i` if `l = -i`. Expanding gives a multilinear
//!   polynomial of degree ≤ k. Falsifying means all literals are
//!   False, i.e., the polynomial evaluates to 1.
//! * A Nullstellensatz certificate of degree `d` is a set of
//!   multipliers `p_i` (each of degree ≤ `d - deg(P_i)`) with the
//!   sum `∑ p_i · P_i = 1` modulo `(x² - x)`. Finding such a
//!   combination reduces to linear algebra over 𝔽₂: the unknowns are
//!   the monomial coefficients of the `p_i`.

pub mod poly;
pub mod ns;
pub mod tseitin;
pub mod propagator;
pub mod php_orbit;
pub mod ns_fp;
pub mod orbit_ns;
pub mod ns_cert;

pub use poly::{Monomial, Poly, F2};
pub use ns::{find_ns_certificate, NsResult, NsCertificate};
pub use tseitin::tseitin_encode_certificate;
pub use propagator::AlgebraicPropagator;
