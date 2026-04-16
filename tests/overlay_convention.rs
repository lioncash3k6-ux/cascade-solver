//! Diagnostic: does satsuma's SAT model for R(4,4)/K_17 pass our
//! propagator's canonicality check?
//!
//! Setup: run satsuma on the R(4,4)/K_17 CNF to extract generators.
//! Build a SymmetryPropagator. Feed it satsuma's known SAT model and
//! ask `check_found_model`. If the propagator REJECTS a model that
//! satsuma considers valid, our convention disagrees with satsuma's.

use cascade::cadical::ExternalPropagator;
use cascade::cardinality::ev;
use cascade::symmetry::satsuma::Satsuma;
use cascade::symmetry::SymmetryPropagator;

fn satsuma_available() -> bool {
    std::path::Path::new("/root/satsuma/satsuma").exists()
}

/// KNOWN FAILURE — documenting, not fixing in v0.6.
///
/// Satsuma's SAT model for R(4,4)/K_17 has MIXED per-generator lex
/// relations: some generators evaluate to `orig > image`, others to
/// `orig < image` under forward-apply. This is inconsistent with ANY
/// strict per-generator lex-leader convention (MIN or MAX). Satsuma's
/// SBP must therefore encode a WEAKER predicate — perhaps one that
/// reasons about the full group rather than individual generators
/// (Schreier-Sims / stabilizer chains), or selectively enforces
/// lex-leader only for "tight" generators.
///
/// Our propagator enforces strict per-generator lex-leader, which is
/// STRICTLY STRONGER. Pure-online mode is sound on its own; overlay
/// mode (SBP + propagator) combines incompatible canonicalities and
/// returns false-UNSAT on SAT instances.
///
/// Resolution: ship pure-online only. Closing overlay is future work
/// (RFC-0002 orbit-closed learning or direct Tseitin encoding of
/// satsuma's specific SBP structure).
#[test]
#[ignore]
fn satsuma_sat_model_passes_our_canonicality() {
    if !satsuma_available() {
        eprintln!("satsuma not installed; skipping");
        return;
    }
    let cnf_path = std::path::Path::new("/root/ramseyproblems/R_4_4_17.cnf");
    if !cnf_path.exists() {
        eprintln!("R(4,4)/K_17 cnf missing; skipping");
        return;
    }

    let scratch = std::env::temp_dir().join("cascade_overlay_diag");
    let satsuma = Satsuma::new();
    // K_17 has C(17,2) = 136 edge vars.
    let (gs, _, _) = satsuma
        .extract_generators(cnf_path, &scratch, 136)
        .expect("extract_generators failed");

    let _ev_unused: i32 = ev(1, 2, 17).raw(); // ensure linkage

    // Satsuma's observed SAT model for R(4,4)/K_17 (from v0.5 run).
    // We recreate it as a DIMACS literal vector. Vars 1..=136 all appear.
    // This literal list was observed from:
    //   ./target/release/cascade R_4_4_17.cnf --biclique
    // If satsuma's branching is deterministic, this model is stable.
    // If not, the test is fragile but still informative.
    #[rustfmt::skip]
    let satsuma_model: Vec<i32> = vec![
        1, 2, 3, 4, 5, -6, -7, -8, -9, -10,
        11, -12, -13, 14, 15, -16, -17, 18, 19, 20,
        -21, -22, 23, -24, -25, -26, 27, 28, -29, -30,
        31, -32, 33, -34, 35, -36, 37, 38, -39, 40,
        41, -42, 43, -44, -45, -46, -47, -48, -49, -50,
        51, 52, 53, -54, 55, 56, -57, 58, -59, -60,
        61, -62, 63, -64, -65, 66, -67, -68, 69, 70,
        71, 72, 73, -74, -75, 76, -77, 78, -79, 80,
        -81, -82, 83, 84, -85, -86, -87, 88, 89, 90,
        91, -92, 93, 94, 95, 96, 97, -98, 99, -100,
        -101, 102, 103, 104, -105, -106, -107, 108, -109, 110,
        -111, 112, -113, -114, 115, 116, 117, -118, 119, 120,
        121, -122, -123, -124, -125, -126, 127, 128, -129, -130,
        131, -132, -133, 134, -135, 136,
    ];

    let mut sym = SymmetryPropagator::new(gs);
    let accepted = sym.check_found_model(&satsuma_model);
    if !accepted {
        panic!(
            "Our propagator REJECTS satsuma's SAT model. \
             Convention mismatch — this is the overlay soundness bug."
        );
    }
}
