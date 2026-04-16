//! Integration test: build Schreier-Sims from satsuma generators and
//! verify group properties on real Ramsey instances.
use cascade::symmetry::schreier_sims::SchreierSims;
use cascade::symmetry::satsuma::Satsuma;
fn satsuma_available() -> bool {
    std::path::Path::new("/root/satsuma/satsuma").exists()
}
#[test]
#[ignore]
fn r33_k6_group_from_satsuma() {
    if !satsuma_available() {
        eprintln!("satsuma not found; skipping");
        return;
    }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_3_6.cnf");
    if !cnf.exists() {
        eprintln!("R_3_3_6.cnf not found; skipping");
        return;
    }
    let scratch = std::env::temp_dir().join("cascade_ss_r33k6");
    let satsuma = Satsuma::new();
    let (gs, _, _) = satsuma.extract_generators(cnf, &scratch, 15).unwrap();
    let base: Vec<u32> = gs.ordering.clone();
    let ss = SchreierSims::build(&gs.gens, &base, 15);
    eprintln!(
        "R(3,3)/K_6: {} input gens → SGS {} gens, group order = {}",
        gs.gens.len(),
        ss.strong_gens.len(),
        ss.group_order()
    );
    // R(3,3)/K_6 has Aut(F) acting on 15 edges. The vertex symmetry
    // group S_6 embeds as S_6 on edges (order 720). With color-swap,
    // order = 1440. Satsuma might detect a subgroup.
    assert!(ss.group_order() >= 2, "expected non-trivial group");
    // Every satsuma generator should be in the group.
    for (i, g) in gs.gens.iter().enumerate() {
        assert!(
            ss.is_member(g, 15),
            "satsuma gen {} not in SS group",
            i
        );
    }
}
#[test]
#[ignore]
fn r34_k9_group_from_satsuma() {
    if !satsuma_available() {
        eprintln!("satsuma not found; skipping");
        return;
    }
    let cnf = std::path::Path::new("/root/SimsPoly/R_3_4_9.cnf");
    if !cnf.exists() {
        return;
    }
    let scratch = std::env::temp_dir().join("cascade_ss_r34k9");
    let satsuma = Satsuma::new();
    let (gs, _, _) = satsuma.extract_generators(cnf, &scratch, 36).unwrap();
    let base: Vec<u32> = gs.ordering.clone();
    let ss = SchreierSims::build(&gs.gens, &base, 36);
    eprintln!(
        "R(3,4)/K_9: {} input gens → SGS {} gens, group order = {}",
        gs.gens.len(),
        ss.strong_gens.len(),
        ss.group_order()
    );
    assert!(ss.group_order() >= 2);
}
