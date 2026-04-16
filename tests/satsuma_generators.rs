//! Integration test for PR-2: end-to-end generator extraction via the
//! real satsuma binary.
//!
//! Writes an R(3,3)/K_6 CNF to a temp file, runs satsuma, parses the
//! resulting VeriPB proof, and asserts the basic shape of the
//! `GeneratorSet`. This is a smoke test rather than an exhaustive one —
//! satsuma's generator output isn't guaranteed stable across versions.
//!
//! Skipped at build-test time on machines without satsuma installed.

use cascade::cardinality::ev;
use cascade::symmetry::satsuma::Satsuma;

fn satsuma_available() -> bool {
    std::path::Path::new("/root/satsuma/satsuma").exists()
}

fn write_r33_k6(path: &std::path::Path) {
    // R(3,3)/K_6 CNF with triangle ban clauses — 15 vars, 40 clauses.
    let n: u32 = 6;
    let mut body = String::from("p cnf 15 40\n");
    for a in 1..=n {
        for b in (a + 1)..=n {
            for c in (b + 1)..=n {
                let eab = ev(a, b, n).raw();
                let eac = ev(a, c, n).raw();
                let ebc = ev(b, c, n).raw();
                body.push_str(&format!("{} {} {} 0\n", -eab, -eac, -ebc));
                body.push_str(&format!("{} {} {} 0\n", eab, eac, ebc));
            }
        }
    }
    std::fs::write(path, body).unwrap();
}

#[test]
fn satsuma_extracts_generators_on_r33_k6() {
    if !satsuma_available() {
        eprintln!("satsuma binary not found at /root/satsuma/satsuma; skipping");
        return;
    }

    let tmp = std::env::temp_dir();
    let cnf = tmp.join("cascade_sat_gen_r33_k6.cnf");
    let scratch = tmp.join("cascade_sat_gen_scratch");
    write_r33_k6(&cnf);

    let satsuma = Satsuma::new();
    let (gs, _aug, _proof) = satsuma
        .extract_generators(&cnf, &scratch, 15)
        .expect("satsuma extract_generators failed");

    // Shape checks (conservative — satsuma's exact generator output can
    // vary across versions):
    //   - n_vars preserved
    //   - ordering non-empty and a permutation of 1..=15
    //   - at least one non-identity generator acts on the 15 edge vars
    //   - (optionally) a color-swap generator: every var flips polarity

    assert_eq!(gs.n_vars, 15);
    assert!(!gs.ordering.is_empty(), "expected non-empty load_order");
    let mut ord_sorted = gs.ordering.clone();
    ord_sorted.sort();
    let expected: Vec<u32> = (1..=15).collect();
    assert_eq!(ord_sorted, expected, "load_order not a permutation of 1..=15");

    assert!(!gs.is_empty(), "expected at least one generator");
    for g in &gs.gens {
        assert_eq!(g.n_vars(), 15);
        assert!(!g.is_identity());
    }

    // For R(3,3)/K_6 satsuma is known to detect the color-swap — at
    // least one generator should have polarity flips.
    let has_color_swap = gs.gens.iter().any(|g| g.has_polarity_flip());
    assert!(has_color_swap, "expected a polarity-flipping generator");
}

#[test]
fn satsuma_extracts_richer_generators_on_r34_k9() {
    if !satsuma_available() {
        eprintln!("satsuma binary not found; skipping");
        return;
    }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_4_9.cnf");
    if !cnf.exists() {
        eprintln!("R_3_4_9.cnf not found on disk; skipping");
        return;
    }

    let scratch = std::env::temp_dir().join("cascade_sat_gen_r34k9");
    let satsuma = Satsuma::new();
    // K_9 has C(9,2) = 36 edge vars.
    let (gs, _, _) = satsuma
        .extract_generators(cnf, &scratch, 36)
        .expect("satsuma extract_generators failed");

    // R(3,4)/K_9 has S_9 vertex symmetry (9! / small factors acting on
    // edges) — satsuma reported 8 generators in manual inspection.
    // We assert "several, not just color-swap", which is a softer bound
    // that survives satsuma version drift.
    assert_eq!(gs.n_vars, 36);
    assert!(
        gs.len() >= 2,
        "expected >=2 generators for R(3,4)/K_9 vertex symmetry, got {}",
        gs.len()
    );
    // Vertex perms don't flip polarity; at least one generator should
    // be polarity-preserving.
    let has_pure_perm = gs.gens.iter().any(|g| !g.has_polarity_flip());
    assert!(has_pure_perm, "expected at least one polarity-preserving generator");
}
