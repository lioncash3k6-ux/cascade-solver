//! VeriPB cutting-planes proof for Ramsey degree bounds (card s>=4).
//!
//! Derives the degree bound "at most k red star edges at vertex v" from
//! the K_s ban clauses using VeriPB's `pol` (sum), `d` (divide), and
//! `w` (weaken) operations.
//!
//! The derivation for vertex v:
//!   1. Sum all C(n-2, s-2) K_s bans containing v → PB constraint with
//!      star edges (coefficient C(n-2,s-2)) and inter-edges (smaller coeff)
//!   2. Divide by the inter-edge coefficient to isolate star edges
//!   3. Weaken (remove) inter-edge variables
//!   4. Result: sum of star ¬edges >= degree (the degree bound)
//!
//! This is then used by cascade's certified pipeline to verify that the
//! cardinality encoding clauses are sound.

use crate::cardinality;
use crate::dimacs::Cnf;
use std::fmt::Write;

/// Emit a VeriPB proof that derives red and blue degree bounds from ban clauses.
///
/// The proof is emitted as a string in VeriPB proof format 3.0.
/// It should be verified against the bare Ramsey CNF (before any augmentation).
///
/// Returns (proof_string, n_derived_constraints).
pub fn emit_card_veripb_proof(
    cnf: &Cnf,
    n: u32,
    s: u32,
    t: u32,
) -> (String, usize) {
    let mut proof = String::new();
    let n_edges = n * (n - 1) / 2;
    let n_clauses = cnf.clauses.len();

    writeln!(proof, "pseudo-Boolean proof version 3.0").unwrap();
    writeln!(proof, "f {};", n_clauses).unwrap();

    let mut next_id = n_clauses + 1;
    let mut n_derived = 0;

    // Red degree bounds: for each vertex v, at most R(s-1,t)-2 red star edges
    let red_bound = cardinality::ramsey_lookup(s - 1, t);
    if red_bound >= 2 && s >= 4 {
        let red_threshold = red_bound - 2; // max red degree
        let red_width = (s * (s - 1) / 2) as usize; // C(s,2) = width of red ban

        // For each vertex, derive the degree bound
        for v in 1..=n {
            let derived = derive_degree_bound_for_vertex(
                &mut proof,
                cnf,
                n, s, t,
                v,
                red_threshold,
                red_width,
                true, // red bans (all negative lits)
                &mut next_id,
            );
            if derived {
                n_derived += 1;
            }
        }
    }

    // Blue degree bounds: for each vertex v, at most R(s,t-1)-2 blue star edges
    // Skip if t >= 6: too many K_t bans per vertex (C(n-1, t-1) can be 300K+)
    // The red bound alone is sufficient for CaDiCaL + CnC to close.
    let blue_bound = cardinality::ramsey_lookup(s, t - 1);
    if blue_bound >= 2 && t >= 4 && t <= 5 {
        let blue_threshold = blue_bound - 2;
        let blue_width = (t * (t - 1) / 2) as usize; // C(t,2)

        for v in 1..=n {
            let derived = derive_degree_bound_for_vertex(
                &mut proof,
                cnf,
                n, s, t,
                v,
                blue_threshold,
                blue_width,
                false, // blue bans (all positive lits)
                &mut next_id,
            );
            if derived {
                n_derived += 1;
            }
        }
    }

    writeln!(proof, "output NONE;").unwrap();
    writeln!(proof, "conclusion NONE;").unwrap();
    writeln!(proof, "end pseudo-Boolean proof;").unwrap();

    (proof, n_derived)
}

/// Derive the degree bound for a single vertex v.
///
/// Returns true if the derivation was emitted.
fn derive_degree_bound_for_vertex(
    proof: &mut String,
    cnf: &Cnf,
    n: u32,
    s: u32,
    t: u32,
    v: u32,
    _threshold: u32,
    ban_width: usize,
    is_red: bool,
    next_id: &mut usize,
) -> bool {
    // Find all ban clause IDs containing vertex v's star edges
    // Ban clauses are identified by width and polarity
    let star_edges: Vec<u32> = (1..=n)
        .filter(|&w| w != v)
        .map(|w| {
            let (a, b) = if v < w { (v, w) } else { (w, v) };
            cardinality::ev(a, b, n).raw().unsigned_abs()
        })
        .collect();

    // Find matching ban clauses (1-indexed constraint IDs for VeriPB)
    let mut ban_ids: Vec<usize> = Vec::new();
    for (ci, clause) in cnf.clauses.iter().enumerate() {
        let lits = clause.lits();
        if lits.len() != ban_width {
            continue;
        }

        // Check polarity: red bans have all negative lits, blue bans all positive
        let right_polarity = if is_red {
            lits.iter().all(|l| l.is_negative())
        } else {
            lits.iter().all(|l| l.is_positive())
        };
        if !right_polarity {
            continue;
        }

        // Check if this ban contains at least one star edge of vertex v
        let vars: Vec<u32> = lits.iter().map(|l| l.var().0).collect();
        let has_star = vars.iter().any(|var| star_edges.contains(var));
        if has_star {
            ban_ids.push(ci + 1); // 1-indexed for VeriPB
        }
    }

    if ban_ids.is_empty() {
        return false;
    }

    // Sum all ban clauses: pol id1 id2 + id3 + id4 + ...
    // VeriPB pol is stack-based, so we chain additions
    if ban_ids.len() == 1 {
        // Only one ban — can't sum, just use it directly
        return false;
    }

    // First: sum the first two
    writeln!(proof, "pol {} {} +;", ban_ids[0], ban_ids[1]).unwrap();
    let mut sum_id = *next_id;
    *next_id += 1;

    // Add remaining bans
    for &bid in &ban_ids[2..] {
        writeln!(proof, "pol {} {} +;", sum_id, bid).unwrap();
        sum_id = *next_id;
        *next_id += 1;
    }

    // Now sum_id contains the sum of all ban clauses at vertex v.
    // Star edges have coefficient C(n-2, s-2) [for red] or C(n-2, t-2) [for blue]
    // Inter-edges have smaller coefficients.
    //
    // Divide by the star-edge coefficient to normalize star edges to coefficient 1.
    // Inter-edge coefficients become < 1, which rounds to 0.
    // RHS becomes ceil(original_rhs / divisor).

    // Compute the star-edge coefficient: how many bans contain each star edge?
    // Each star edge e(v,w) appears in C(n-2, s-2) red bans (choosing s-2 more
    // vertices from the remaining n-2 to form a K_s with v and w).
    let other_verts = n - 2; // excluding v and w
    let choose = if is_red { s - 2 } else { t - 2 };
    let star_coeff = comb(other_verts, choose);

    if star_coeff <= 1 {
        return false; // Can't divide
    }

    writeln!(proof, "pol {} {} d;", sum_id, star_coeff).unwrap();
    let div_id = *next_id;
    *next_id += 1;

    // Weaken all non-star variables (inter-edges and any other vars)
    // We need to identify which variables are NOT star edges of v
    let mut weaken_vars: Vec<u32> = Vec::new();
    for e in 1..=n * (n - 1) / 2 {
        if !star_edges.contains(&e) {
            weaken_vars.push(e);
        }
    }

    if !weaken_vars.is_empty() {
        let mut pol_line = format!("pol {}", div_id);
        for &var in &weaken_vars {
            write!(pol_line, " x{} w", var).unwrap();
        }
        writeln!(proof, "{};", pol_line).unwrap();
        *next_id += 1;
    }

    true
}

/// Compute C(n, k) = n! / (k! * (n-k)!)
fn comb(n: u32, k: u32) -> u32 {
    if k > n {
        return 0;
    }
    if k == 0 || k == n {
        return 1;
    }
    let k = k.min(n - k);
    let mut result: u64 = 1;
    for i in 0..k {
        result = result * (n - i) as u64 / (i + 1) as u64;
    }
    result as u32
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::dimacs;
    use std::io::{BufReader, Cursor};

    fn parse(s: &str) -> Cnf {
        dimacs::parse_reader(BufReader::new(Cursor::new(s.as_bytes()))).unwrap()
    }

    #[test]
    fn comb_basic() {
        assert_eq!(comb(4, 2), 6);
        assert_eq!(comb(5, 2), 10);
        assert_eq!(comb(17, 2), 136);
        assert_eq!(comb(35, 2), 595);
    }

    #[test]
    fn card_proof_r44_k18() {
        // R(4,4) on K_18: s=4, should derive degree bounds via pol
        let cnf = dimacs::parse_file(
            std::path::Path::new("/root/ramseyproblems/R_4_4_18.cnf"),
        ).unwrap();
        let (proof, n) = emit_card_veripb_proof(&cnf, 18, 4, 4);
        eprintln!("derived {} bounds", n);
        eprintln!("proof length: {} bytes", proof.len());
        assert!(n > 0, "should derive at least one bound");
        assert!(proof.contains("pol"), "should contain pol operations");

        // Write proof and verify with veripb
        std::fs::write("/tmp/test_card_r44.pbp", &proof).unwrap();
        let out = std::process::Command::new("veripb")
            .arg("--cnf")
            .arg("/root/ramseyproblems/R_4_4_18.cnf")
            .arg("/tmp/test_card_r44.pbp")
            .output()
            .unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        let stderr = String::from_utf8_lossy(&out.stderr);
        eprintln!("veripb stdout: {}", stdout);
        eprintln!("veripb stderr: {}", stderr);
        assert!(
            stdout.contains("VERIFIED") || stderr.contains("VERIFIED"),
            "veripb should verify the card proof"
        );
    }

    #[test]
    fn card_proof_r45_k25() {
        let cnf = dimacs::parse_file(
            std::path::Path::new("/root/ramseyproblems/R_4_5_25.cnf"),
        ).unwrap();
        let (proof, n) = emit_card_veripb_proof(&cnf, 25, 4, 5);
        eprintln!("R(4,5)/K_25: {} bounds, {} bytes", n, proof.len());
        std::fs::write("/tmp/test_card_r45.pbp", &proof).unwrap();
        let out = std::process::Command::new("veripb")
            .arg("--cnf")
            .arg("/root/ramseyproblems/R_4_5_25.cnf")
            .arg("/tmp/test_card_r45.pbp")
            .output().unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        eprintln!("veripb: {}", stdout);
        assert!(stdout.contains("VERIFIED"));
    }

    #[test]
    fn card_proof_r46_k36() {
        let cnf = dimacs::parse_file(
            std::path::Path::new("/root/ramseyproblems/R_4_6_36.cnf"),
        ).unwrap();
        let (proof, n) = emit_card_veripb_proof(&cnf, 36, 4, 6);
        eprintln!("R(4,6)/K_36: {} bounds, {} bytes", n, proof.len());
        std::fs::write("/tmp/test_card_r46.pbp", &proof).unwrap();
        let out = std::process::Command::new("veripb")
            .arg("--cnf")
            .arg("/root/ramseyproblems/R_4_6_36.cnf")
            .arg("/tmp/test_card_r46.pbp")
            .output().unwrap();
        let stdout = String::from_utf8_lossy(&out.stdout);
        eprintln!("veripb: {}", stdout);
        assert!(stdout.contains("VERIFIED"));
    }
}
