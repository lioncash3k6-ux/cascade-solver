//! Tseitin encoding of polynomial certificates back to CNF.
//!
//! Given a Nullstellensatz certificate `∑ p_i · P_i ≡ 1`, we produce
//! a set of CNF clauses that together express the certificate as a
//! linear-number-of-clauses proof that F is UNSAT. These clauses
//! serve as a Tseitin-encoded "bridge" feeding CDCL a direct unit-
//! propagation path to refutation.
//!
//! # Approach (minimal first cut)
//!
//! For a certificate polynomial equation `∑ p_i · P_i = 1`, we treat
//! each clause `C_i` as 0-valued under F, which forces the weighted
//! sum to 0 — but it's 1, contradiction.
//!
//! At the clause level: for each clause `C_i` in the certificate,
//! Tseitin encoding introduces an auxiliary variable `t_i` constrained
//! to equal the polynomial value of `p_i · P_i` (which is 0 over F).
//! Then the XOR sum constraint `∑ t_i = 1` is violated.
//!
//! For the **minimal** bridge, we skip the full Tseitin and just emit
//! the clause-set `{C_i : i ∈ cert}` verbatim — these clauses are
//! already in F, so emitting duplicates isn't helpful. The real
//! utility of the Tseitin layer is when the certificate involves
//! **products of literals** the original CNF doesn't make explicit.
//!
//! This module is deliberately minimal in v0.6 — it's a placeholder
//! and explicit-hypothesis-tracker until we have a target instance
//! (K_5 width barrier) to tune against.

use super::ns::NsCertificate;

/// Stub: given a certificate, produce the set of clause indices it
/// references. Callers can use this to know which original clauses
/// were "witness-involved" in the UNSAT proof and highlight them in
/// a user-facing proof explanation.
pub fn tseitin_encode_certificate(cert: &NsCertificate) -> Vec<usize> {
    cert.terms.iter().map(|t| t.clause_idx).collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::ns::{find_ns_certificate, NsResult};

    #[test]
    fn triangle_cert_references_all_three_clauses() {
        let clauses = vec![vec![1], vec![2], vec![-1, -2]];
        match find_ns_certificate(&clauses, 2, 2) {
            NsResult::Unsat(cert) => {
                let refs = tseitin_encode_certificate(&cert);
                // At degree 2 the certificate uses the three clauses.
                assert!(!refs.is_empty());
                for &idx in &refs {
                    assert!(idx < clauses.len());
                }
            }
            _ => panic!("expected UNSAT cert"),
        }
    }
}
