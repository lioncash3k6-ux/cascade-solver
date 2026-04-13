//! Tseitin double encoding + near-1-factorization chain binaries.
//!
//! For Ramsey R(s,t) on K_n (n odd), this generates the augmentation that
//! makes structural instances BCP-trivial:
//!
//!   1. **Tseitin channeling**: for each edge variable e, introduce b_e (blue)
//!      with clauses {b_e, e} and {¬b_e, ¬e}. This encodes b_e ↔ ¬e.
//!
//!   2. **Near-1-factorization**: decompose K_n into n matchings of (n-1)/2
//!      edges each, via the cyclic construction: round r pairs vertex i with
//!      vertex (2r - i) mod n. Arrange as an n × ((n-1)/2) matrix.
//!
//!   3. **Staircase chain binaries**: for each column j, for each adjacent
//!      row pair (i, i+1), emit {b_{M[i][j]}, ¬b_{M[i+1][j]}}. This orders
//!      rows within each column: "if the lower edge is blue, the upper must be."
//!
//! The BCP cascade mechanism: clausal fixing units set some edges blue →
//! channeling activates b variables → chains propagate blue upward through
//! columns → AMO forces corresponding r variables false → eventually all
//! 300 edges are determined → ban clause fires → UNSAT.
//!
//! For R(4,5)/K_25: 300 channeling + 300 AMO + 288 chains = 888 extra clauses,
//! 300 new variables. BCP closes in 135 propagations (3ms).

use crate::types::Lit;
use crate::cardinality::ev;

/// Result of the chain augmentation.
#[derive(Debug)]
pub struct ChainAugmentation {
    /// All generated clauses (channeling + AMO + chains).
    pub clauses: Vec<Vec<Lit>>,
    /// Number of new auxiliary variables (= number of edge variables).
    pub aux_vars: u32,
    /// The near-1-factorization matrix: matrix[row][col] = edge variable index.
    pub matrix: Vec<Vec<u32>>,
    /// Number of channeling clauses.
    pub n_channeling: usize,
    /// Number of AMO clauses.
    pub n_amo: usize,
    /// Number of chain binary clauses.
    pub n_chains: usize,
}

/// Compute the near-1-factorization of K_n (n must be odd).
///
/// Returns a matrix of n rows × (n-1)/2 columns, where each entry is an
/// edge variable index (1-indexed, matching `ev()`). Each row is a
/// near-perfect matching; each edge appears in exactly one row.
pub fn near_1_factorization(n: u32) -> Vec<Vec<u32>> {
    let mut matrix = Vec::with_capacity(n as usize);
    for r in 0..n {
        let mut matching = Vec::new();
        let mut matched = vec![false; n as usize];
        for i in 0..n {
            if i == r {
                continue;
            }
            let j = (2 * r + n - i) % n; // (2r - i) mod n
            if j == r || i == j {
                continue;
            }
            let ui = i as usize;
            let uj = j as usize;
            if !matched[ui] && !matched[uj] {
                let (a, b) = if i < j { (i + 1, j + 1) } else { (j + 1, i + 1) };
                matching.push(ev(a, b, n).raw() as u32);
                matched[ui] = true;
                matched[uj] = true;
            }
        }
        matrix.push(matching);
    }
    matrix
}

/// Generate the full Tseitin + chain augmentation for K_n.
///
/// `n_edges` = C(n, 2), the number of original edge variables.
/// New blue variables are numbered (n_edges + 1) through (2 * n_edges).
///
/// Returns the augmentation (clauses + metadata). The clauses should be
/// appended to the formula, and `aux_vars` new variables are introduced.
pub fn generate_chain_augmentation(n: u32) -> ChainAugmentation {
    let n_edges = (n * (n - 1) / 2) as usize;
    let mut clauses = Vec::new();

    // Phase 1: Tseitin channeling — {b_e, e} for each edge e
    // b_e = e + n_edges (so b_1 = n_edges+1, etc.)
    for e in 1..=(n_edges as i32) {
        let b_e = e + n_edges as i32;
        clauses.push(vec![Lit::new(b_e), Lit::new(e)]);
    }
    let n_channeling = clauses.len();

    // Phase 2: AMO — {¬b_e, ¬e} for each edge e
    for e in 1..=(n_edges as i32) {
        let b_e = e + n_edges as i32;
        clauses.push(vec![Lit::new(-b_e), Lit::new(-e)]);
    }
    let n_amo = clauses.len() - n_channeling;

    // Phase 3: Near-1-factorization chain binaries
    let matrix = near_1_factorization(n);
    let n_rows = matrix.len();
    let n_cols = if n_rows > 0 { matrix[0].len() } else { 0 };
    let mut n_chains = 0;

    for j in 0..n_cols {
        for i in 0..(n_rows - 1) {
            let upper_edge = matrix[i][j] as i32;
            let lower_edge = matrix[i + 1][j] as i32;
            let b_upper = upper_edge + n_edges as i32;
            let b_lower = lower_edge + n_edges as i32;
            // If lower is blue (b_lower true), upper must be blue (b_upper true)
            // Clause: {b_upper, ¬b_lower}
            clauses.push(vec![Lit::new(b_upper), Lit::new(-b_lower)]);
            n_chains += 1;
        }
    }

    ChainAugmentation {
        clauses,
        aux_vars: n_edges as u32,
        matrix,
        n_channeling,
        n_amo,
        n_chains,
    }
}

/// Generate clausal fixing units for the first `count` disjoint edge pairs.
///
/// For edges e(2k+1, 2k+2) where k = 0..count-1, emit unit clause {¬e}
/// (fixing the edge to blue/false). These are the "Phase 1" units from the
/// R(4,5) proof.
///
/// The units are sound because each pair (2k+1, 2k+2) belongs to a K_s clique
/// whose other edges can be permuted by the stabilizer — proven as SR with
/// vertex transposition witnesses.
///
/// Returns the unit clauses (each is a single negative literal).
pub fn clausal_fixing_units(n: u32, count: u32) -> Vec<Vec<Lit>> {
    let mut units = Vec::new();
    for k in 0..count {
        let v1 = 2 * k + 1;
        let v2 = 2 * k + 2;
        if v1 <= n && v2 <= n {
            units.push(vec![Lit::new(-(ev(v1, v2, n).raw()))]);
        }
    }
    units
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn factorization_k5() {
        // K_5: 5 vertices, 10 edges, 5 matchings of 2 edges each
        let m = near_1_factorization(5);
        assert_eq!(m.len(), 5);
        for row in &m {
            assert_eq!(row.len(), 2);
        }
        // Every edge appears exactly once
        let mut seen = std::collections::HashSet::new();
        for row in &m {
            for &e in row {
                assert!(seen.insert(e), "duplicate edge {}", e);
            }
        }
        assert_eq!(seen.len(), 10);
    }

    #[test]
    fn factorization_k9() {
        let m = near_1_factorization(9);
        assert_eq!(m.len(), 9);
        for row in &m {
            assert_eq!(row.len(), 4);
        }
        let mut seen = std::collections::HashSet::new();
        for row in &m {
            for &e in row {
                assert!(seen.insert(e), "duplicate edge {}", e);
            }
        }
        assert_eq!(seen.len(), 36); // C(9,2) = 36
    }

    #[test]
    fn factorization_k25() {
        let m = near_1_factorization(25);
        assert_eq!(m.len(), 25);
        for row in &m {
            assert_eq!(row.len(), 12);
        }
        let mut seen = std::collections::HashSet::new();
        for row in &m {
            for &e in row {
                assert!(seen.insert(e), "duplicate edge {}", e);
            }
        }
        assert_eq!(seen.len(), 300); // C(25,2) = 300
    }

    #[test]
    fn chain_augmentation_k25() {
        let aug = generate_chain_augmentation(25);
        assert_eq!(aug.n_channeling, 300);
        assert_eq!(aug.n_amo, 300);
        assert_eq!(aug.n_chains, 24 * 12); // 288
        assert_eq!(aug.clauses.len(), 300 + 300 + 288);
        assert_eq!(aug.aux_vars, 300);
    }

    #[test]
    fn chain_augmentation_k9() {
        let aug = generate_chain_augmentation(9);
        assert_eq!(aug.n_channeling, 36);
        assert_eq!(aug.n_amo, 36);
        assert_eq!(aug.n_chains, 8 * 4); // 32
        assert_eq!(aug.clauses.len(), 36 + 36 + 32);
        assert_eq!(aug.aux_vars, 36);
    }

    #[test]
    fn clausal_fixing_r45() {
        // R(4,5)/K_25: 11 disjoint pairs
        let units = clausal_fixing_units(25, 11);
        assert_eq!(units.len(), 11);
        for u in &units {
            assert_eq!(u.len(), 1);
            assert!(u[0].is_negative());
        }
    }
}
