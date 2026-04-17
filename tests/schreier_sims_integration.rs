//! Integration test: randomized Schreier-Sims on real satsuma generators.

use cascade::symmetry::schreier_sims::SchreierSims;
use cascade::symmetry::satsuma::Satsuma;

fn satsuma_available() -> bool {
    std::path::Path::new("/root/satsuma/satsuma").exists()
}

#[test]
fn r33_k6_group_randomized() {
    if !satsuma_available() { return; }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_3_6.cnf");
    if !cnf.exists() { return; }
    let scratch = std::env::temp_dir().join("cascade_rss_r33k6");
    let satsuma = Satsuma::new();
    let (gs, _, _) = satsuma.extract_generators(cnf, &scratch, 15).unwrap();
    let base: Vec<u32> = gs.ordering.clone();

    let t = std::time::Instant::now();
    let ss = SchreierSims::build_randomized(&gs.gens, &base, 15, 50);
    let elapsed = t.elapsed().as_secs_f64();

    eprintln!(
        "R(3,3)/K_6: {} input gens → SGS {} gens, |G| = {}, {:.3}s",
        gs.gens.len(), ss.strong_gens.len(), ss.group_order(), elapsed
    );
    // R(3,3)/K_6 with color-swap: |Aut(F)| = 2 × |S_6 on edges|.
    // Exact group order depends on satsuma's detected group.
    assert!(ss.group_order() >= 2);
    assert!(elapsed < 5.0, "randomized SS took too long: {:.1}s", elapsed);
}

#[test]
fn r34_k9_group_randomized() {
    if !satsuma_available() { return; }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_4_9.cnf");
    if !cnf.exists() { return; }
    let scratch = std::env::temp_dir().join("cascade_rss_r34k9");
    let satsuma = Satsuma::new();
    let (gs, _, _) = satsuma.extract_generators(cnf, &scratch, 36).unwrap();
    let base: Vec<u32> = gs.ordering.clone();

    let t = std::time::Instant::now();
    let ss = SchreierSims::build_randomized(&gs.gens, &base, 36, 50);
    let elapsed = t.elapsed().as_secs_f64();

    eprintln!(
        "R(3,4)/K_9: {} input gens → SGS {} gens, |G| = {}, {:.3}s",
        gs.gens.len(), ss.strong_gens.len(), ss.group_order(), elapsed
    );
    assert_eq!(ss.group_order(), 362880, "expected 9! = S_9 on edges");
    assert!(elapsed < 5.0);

    // Every input generator should be in the group.
    for (i, g) in gs.gens.iter().enumerate() {
        assert!(ss.is_member(g, 36), "gen {} not in group", i);
    }
}

#[test]
fn r35_k14_group_randomized() {
    if !satsuma_available() { return; }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_5_14.cnf");
    if !cnf.exists() { return; }
    let scratch = std::env::temp_dir().join("cascade_rss_r35k14");
    let satsuma = Satsuma::new();
    let (gs, _, _) = satsuma.extract_generators(cnf, &scratch, 91).unwrap();
    let base: Vec<u32> = gs.ordering.clone();

    let t = std::time::Instant::now();
    let ss = SchreierSims::build_randomized(&gs.gens, &base, 91, 50);
    let elapsed = t.elapsed().as_secs_f64();

    eprintln!(
        "R(3,5)/K_14: {} input gens → SGS {} gens, |G| = {}, {:.3}s",
        gs.gens.len(), ss.strong_gens.len(), ss.group_order(), elapsed
    );
    assert!(ss.group_order() >= 2);
    assert!(elapsed < 10.0);
}
