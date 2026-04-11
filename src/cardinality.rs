//! Cardinality CNF encoding via sequential counter (Sinz 2005).
//!
//! Used for Ramsey degree bounds: at every vertex, the red and blue degrees
//! must lie in specific ranges derived from R(s-1,t) and R(s,t-1).
//!
//! For each vertex v of K_n with R(s,t) being the target Ramsey number:
//!   red_degree(v)  <= R(s-1, t) - 1
//!   blue_degree(v) <= R(s, t-1) - 1
//!
//! These bounds are theorems of the bare CNF (link-graph argument). Adding
//! them as additional clauses preserves equisatisfiability with the bare
//! CNF, but the proof of equisatisfiability is NOT currently emitted —
//! it's the same gap as the chain binaries in the manual 3-file proof.
//!
//! The sequential counter encoding produces clauses of these types:
//!   (1) ¬x_i ∨ s_{i,1}                     (introduce counter aux at position i)
//!   (2) ¬s_{i-1,j} ∨ s_{i,j}               (monotonicity of running sum)
//!   (3) ¬x_i ∨ ¬s_{i-1,j-1} ∨ s_{i,j}      (increment when x_i is true)
//!   (4) ¬x_i ∨ ¬s_{i-1,k}                  (forbid exceeding the bound k)
//!
//! Types (1)–(3) are RAT-on-fresh-aux trivially. Type (4) is the actual bound
//! enforcement and is the only one whose soundness depends on the Ramsey theorem.

use crate::types::Lit;

/// Output of a single cardinality encoding step.
#[derive(Debug)]
pub struct CardEncoding {
    /// All generated clauses (each as a Vec<Lit>).
    pub clauses: Vec<Vec<Lit>>,
    /// Number of fresh auxiliary variables introduced.
    pub aux_vars: u32,
    /// Range [base+1, base+aux_vars] of fresh aux variables.
    pub aux_base: u32,
}

/// Sequential counter at-most-k encoding (Sinz 2005).
///
/// Given variables `lits[0..n]` and bound `k`, generates clauses asserting
/// that at most `k` of the variables can be simultaneously true. Allocates
/// fresh auxiliary variables starting at `next_aux_base + 1`.
///
/// Returns the encoding (clauses + how many fresh vars were used).
pub fn encode_at_most_k(lits: &[Lit], k: u32, next_aux_base: u32) -> CardEncoding {
    let n = lits.len();
    let k_us = k as usize;
    if k_us >= n {
        // Trivially satisfied
        return CardEncoding {
            clauses: Vec::new(),
            aux_vars: 0,
            aux_base: next_aux_base,
        };
    }

    let mut clauses: Vec<Vec<Lit>> = Vec::new();

    // s[i][j] for i in 0..n, j in 0..k. Layout: aux_base + i*k + j (0-indexed → +1 for 1-indexed lit)
    let s = |i: usize, j: usize| -> Lit {
        let raw = next_aux_base as i32 + (i * k_us + j) as i32 + 1;
        Lit::new(raw)
    };

    // Position 0: x_0 → s(0, 0)
    clauses.push(vec![lits[0].negate(), s(0, 0)]);
    // and forbid s(0, j) for j > 0
    for j in 1..k_us {
        clauses.push(vec![s(0, j).negate()]);
    }

    // Positions 1..n-1
    for i in 1..n {
        // x_i → s(i, 0)
        clauses.push(vec![lits[i].negate(), s(i, 0)]);
        // s(i-1, 0) → s(i, 0)
        clauses.push(vec![s(i - 1, 0).negate(), s(i, 0)]);
        // x_i ∧ s(i-1, k-1) → ⊥
        clauses.push(vec![lits[i].negate(), s(i - 1, k_us - 1).negate()]);
        // For each level j in 1..k-1
        for j in 1..k_us {
            // x_i ∧ s(i-1, j-1) → s(i, j)
            clauses.push(vec![lits[i].negate(), s(i - 1, j - 1).negate(), s(i, j)]);
            // s(i-1, j) → s(i, j)
            clauses.push(vec![s(i - 1, j).negate(), s(i, j)]);
        }
    }

    let aux_used = (n * k_us) as u32;

    CardEncoding {
        clauses,
        aux_vars: aux_used,
        aux_base: next_aux_base,
    }
}

/// Build the Ramsey edge variable index `(i,j)` (1 ≤ i < j ≤ n).
/// Standard upper-triangular row-major encoding matching all our generators.
#[inline]
pub fn ev(i: u32, j: u32, n: u32) -> Lit {
    let (a, b) = if i < j { (i, j) } else { (j, i) };
    let idx = (a - 1) * (2 * n - a) / 2 + (b - a);
    Lit::new(idx as i32)
}

/// Generate the full Ramsey degree-bound cardinality CNF for R(s,t) at K_n.
///
/// Inserts at-most-k constraints for both red and blue degree at every vertex.
/// `next_aux_base` is the highest variable currently in the formula; new aux
/// vars are allocated starting from next_aux_base+1.
///
/// Returns: (all clauses, total aux vars added, final next_aux_base)
pub fn ramsey_card_cnf(
    n: u32,
    max_red_deg: u32,
    max_blue_deg: u32,
    next_aux_base: u32,
) -> (Vec<Vec<Lit>>, u32, u32) {
    let mut all_clauses = Vec::new();
    let mut base = next_aux_base;
    let mut total_aux = 0u32;

    for v in 1..=n {
        // Edge literals incident to v
        let edges: Vec<Lit> = (1..=n)
            .filter(|&w| w != v)
            .map(|w| ev(v, w, n))
            .collect();

        // Red degree ≤ max_red_deg: at-most-k over positive literals
        if (max_red_deg as usize) < edges.len() {
            let enc = encode_at_most_k(&edges, max_red_deg, base);
            base += enc.aux_vars;
            total_aux += enc.aux_vars;
            all_clauses.extend(enc.clauses);
        }

        // Blue degree ≤ max_blue_deg: at-most-k over NEGATED literals
        if (max_blue_deg as usize) < edges.len() {
            let neg_edges: Vec<Lit> = edges.iter().map(|l| l.negate()).collect();
            let enc = encode_at_most_k(&neg_edges, max_blue_deg, base);
            base += enc.aux_vars;
            total_aux += enc.aux_vars;
            all_clauses.extend(enc.clauses);
        }
    }

    (all_clauses, total_aux, base)
}

/// Lookup table for Ramsey numbers used in the degree bound computation.
/// Returns 0 for unknown values, in which case the caller should fall back
/// to "no bound" (i.e., use n - 1 trivially).
pub fn ramsey_lookup(a: u32, b: u32) -> u32 {
    let (a, b) = if a <= b { (a, b) } else { (b, a) };
    if a == 0 {
        return 0;
    }
    if a == 1 {
        return 1;
    }
    if a == 2 {
        return b;
    }
    if a == 3 {
        return match b {
            3 => 6,
            4 => 9,
            5 => 14,
            6 => 18,
            7 => 23,
            8 => 28,
            9 => 36,
            _ => 0,
        };
    }
    if a == 4 {
        return match b {
            4 => 18,
            5 => 25,
            6 => 41,
            _ => 0,
        };
    }
    if a == 5 {
        return match b {
            5 => 43,
            6 => 87,
            _ => 0,
        };
    }
    0
}

/// Auto-detect a Ramsey instance from the variable count: nvars = C(n, 2).
/// Returns Some(n) if nvars matches a triangular number, else None.
pub fn detect_ramsey_n(nvars: u32) -> Option<u32> {
    if nvars < 1 {
        return None;
    }
    // Solve n*(n-1)/2 = nvars  →  n = (1 + sqrt(1 + 8*nvars)) / 2
    let f = ((1.0 + (1.0_f64 + 8.0 * nvars as f64).sqrt()) / 2.0).round() as u32;
    if f * (f - 1) / 2 == nvars {
        Some(f)
    } else {
        None
    }
}

/// Auto-detect Ramsey (s, t) from clause widths in the CNF.
/// `min_neg_width` and `min_pos_width` are the smallest all-negative and
/// all-positive clause widths in the formula. These correspond to the K_s
/// and K_t cliques being forbidden, with width = C(k, 2) for K_k.
pub fn detect_ramsey_st(min_neg_width: u32, min_pos_width: u32) -> Option<(u32, u32)> {
    let width_to_k = |w: u32| -> Option<u32> {
        // w = k*(k-1)/2  →  k = (1 + sqrt(1 + 8w)) / 2
        if w == 0 {
            return None;
        }
        let f = ((1.0 + (1.0_f64 + 8.0 * w as f64).sqrt()) / 2.0).round() as u32;
        if f * (f - 1) / 2 == w {
            Some(f)
        } else {
            None
        }
    };
    let s = width_to_k(min_neg_width)?;
    let t = width_to_k(min_pos_width)?;
    Some((s, t))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ev_basics() {
        // K_5: edges (1,2), (1,3), ..., (4,5), 10 in total
        assert_eq!(ev(1, 2, 5), Lit::new(1));
        assert_eq!(ev(1, 5, 5), Lit::new(4));
        assert_eq!(ev(4, 5, 5), Lit::new(10));
    }

    #[test]
    fn detect_n_from_nvars() {
        assert_eq!(detect_ramsey_n(10), Some(5));
        assert_eq!(detect_ramsey_n(15), Some(6));
        assert_eq!(detect_ramsey_n(153), Some(18));
        assert_eq!(detect_ramsey_n(300), Some(25));
        assert_eq!(detect_ramsey_n(861), Some(42));
        assert_eq!(detect_ramsey_n(903), Some(43));
        assert_eq!(detect_ramsey_n(11), None);  // not triangular
    }

    #[test]
    fn detect_st_from_widths() {
        // K_4 = 6 lits, K_5 = 10 lits
        assert_eq!(detect_ramsey_st(6, 10), Some((4, 5)));  // R(4,5)
        assert_eq!(detect_ramsey_st(6, 6), Some((4, 4)));   // R(4,4)
        assert_eq!(detect_ramsey_st(3, 10), Some((3, 5)));  // R(3,5)
    }

    #[test]
    fn ramsey_lookup_smoke() {
        assert_eq!(ramsey_lookup(3, 3), 6);
        assert_eq!(ramsey_lookup(4, 4), 18);
        assert_eq!(ramsey_lookup(4, 5), 25);
        assert_eq!(ramsey_lookup(5, 5), 43);
        assert_eq!(ramsey_lookup(99, 99), 0);  // unknown
    }

    #[test]
    fn at_most_k_smoke() {
        // 5 vars, at most 2 true
        let lits: Vec<Lit> = (1..=5).map(Lit::new).collect();
        let enc = encode_at_most_k(&lits, 2, 5);
        // Sequential counter with n=5, k=2 should produce ~30 clauses
        assert!(!enc.clauses.is_empty());
        // Aux vars: n * k = 10
        assert_eq!(enc.aux_vars, 10);
        // First aux var should be 6
        assert_eq!(enc.aux_base, 5);
    }

    #[test]
    fn r45_card_count() {
        // R(4,5) at K_25: max_red = R(3,5)-1 = 13, max_blue = R(4,4)-1 = 17
        // n = 25, edges per vertex = 24
        // Per vertex per bound: ~ n*k clauses; per vertex total ~ 25*13 + 25*17 ≈ 750 clauses
        let (clauses, aux, _) = ramsey_card_cnf(25, 13, 17, 300);
        assert!(!clauses.is_empty());
        assert!(aux > 0);
        // Sanity: nontrivial size
        assert!(clauses.len() > 1000);
    }
}
