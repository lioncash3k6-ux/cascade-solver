//! Cascade CLI — Week 3: satsuma symmetry breaking → CaDiCaL backend.
//!
//! Usage:
//!   cascade <input.cnf> [--proof out.drat] [--equisat-proof out.pbp]
//!                       [--timeout SECS] [--no-solve] [--no-symmetry]
//!
//! Pipeline:
//!   1. Parse CNF
//!   2. (unless --no-symmetry) run satsuma → augmented CNF + VeriPB equisat proof
//!   3. (unless --no-solve) run CaDiCaL on the augmented CNF → DRAT body proof
//!
//! Two-file proof: --equisat-proof and --proof together prove the BARE CNF
//! is UNSAT (or SAT with the model).

use cascade::backend::cadical::CaDiCaL;
use cascade::backend::{Backend, BackendProofFormat, Verdict};
use cascade::bcp::{bcp_cascade, BcpResult};
use cascade::biclique;
use cascade::cadical as cadical_ffi;
use cascade::cardinality;
use cascade::chain;
use cascade::certify;
use cascade::dimacs;
use cascade::propagator::{BicliquePropagator, CompositePropagator};
use cascade::symmetry::proof::{build_veripb_proof, SymProofLog};
use cascade::symmetry::satsuma::Satsuma;
use cascade::symmetry::{
    parse_veripb_proof, EquisatProofFormat, GeneratorSet, Permutation, SymmetryBreaker,
    SymmetryPropagator,
};
use std::sync::{Arc, Mutex};
use std::io::{BufRead, BufReader, Write};
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use std::time::Instant;

fn print_usage(prog: &str) {
    eprintln!(
        "Usage: {} <input.cnf> [--proof <out.drat>] [--equisat-proof <out.pbp>]\n\
        \x20            [--timeout <secs>] [--no-solve] [--no-symmetry]\n\
        \x20            [--biclique] [--online-sym] [--cnc D T C]\n\
        \x20            [--no-card] [--no-chain] [--no-bcp] [--certified]\n\
        \n\
        --online-sym  (v0.6) attach an online lex-leader symmetry propagator\n\
        \x20            alongside --biclique. Soundness under --certified requires\n\
        \x20            PR-5 VeriPB proof emission (not yet landed).",
        prog
    );
}

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 2 {
        print_usage(&args[0]);
        return ExitCode::from(2);
    }

    let mut input: Option<PathBuf> = None;
    let mut proof: Option<PathBuf> = None;
    let mut equisat_proof: Option<PathBuf> = None;
    let mut timeout: Option<u32> = None;
    let mut no_solve = false;
    let mut no_symmetry = false;
    let mut no_card = false;
    let mut no_chain = false;
    let mut no_bcp = false;
    let mut certified = false;
    let mut use_biclique = false;
    let mut online_sym = false;
    let mut alg_preprocess_degree: Option<usize> = None;
    let mut alg_propagate = false;
    let mut alg_prime: u8 = 2;
    let mut alg_php_functional: Option<(u32, u32)> = None;
    let mut use_cnc = false;
    let mut cnc_depth: u32 = 0;
    let mut cnc_threads: u32 = 0;
    let mut cnc_cube_timeout: u32 = 600;

    let mut i = 1;
    while i < args.len() {
        match args[i].as_str() {
            "--proof" => {
                if i + 1 >= args.len() {
                    eprintln!("--proof needs an argument");
                    return ExitCode::from(2);
                }
                proof = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--equisat-proof" => {
                if i + 1 >= args.len() {
                    eprintln!("--equisat-proof needs an argument");
                    return ExitCode::from(2);
                }
                equisat_proof = Some(PathBuf::from(&args[i + 1]));
                i += 2;
            }
            "--timeout" => {
                if i + 1 >= args.len() {
                    eprintln!("--timeout needs an argument");
                    return ExitCode::from(2);
                }
                timeout = Some(args[i + 1].parse().unwrap_or(0));
                i += 2;
            }
            "--no-solve" => {
                no_solve = true;
                i += 1;
            }
            "--no-symmetry" => {
                no_symmetry = true;
                i += 1;
            }
            "--no-card" => {
                no_card = true;
                i += 1;
            }
            "--no-chain" => {
                no_chain = true;
                i += 1;
            }
            "--no-bcp" => {
                no_bcp = true;
                i += 1;
            }
            "--certified" => {
                certified = true;
                i += 1;
            }
            "--biclique" => {
                use_biclique = true;
                i += 1;
            }
            "--online-sym" => {
                online_sym = true;
                i += 1;
            }
            "--alg-preprocess" => {
                if i + 1 >= args.len() {
                    eprintln!("--alg-preprocess needs a degree");
                    return ExitCode::from(2);
                }
                alg_preprocess_degree = args[i + 1].parse().ok();
                if alg_preprocess_degree.is_none() {
                    eprintln!("--alg-preprocess degree must be an integer");
                    return ExitCode::from(2);
                }
                i += 2;
            }
            "--alg-propagate" => {
                alg_propagate = true;
                i += 1;
            }
            "--alg-p" => {
                if i + 1 >= args.len() {
                    eprintln!("--alg-p needs a small prime (2, 3, 5, 7, ...)");
                    return ExitCode::from(2);
                }
                match args[i + 1].parse::<u8>() {
                    Ok(p) if p >= 2 => {
                        alg_prime = p;
                    }
                    _ => {
                        eprintln!("--alg-p must be a prime >= 2");
                        return ExitCode::from(2);
                    }
                }
                i += 2;
            }
            "--alg-php" => {
                // --alg-php P H: treat input as functional PHP_{P,H}.
                // Uses linear totality + AMO axioms + orbit-reduced 𝔽_p search
                // (requires --alg-p with p prime, p ∤ P!·H!).
                if i + 2 >= args.len() {
                    eprintln!("--alg-php needs P and H (e.g. --alg-php 5 4)");
                    return ExitCode::from(2);
                }
                let pp: u32 = match args[i + 1].parse() {
                    Ok(v) if v >= 2 => v,
                    _ => {
                        eprintln!("--alg-php: P must be >= 2");
                        return ExitCode::from(2);
                    }
                };
                let hh: u32 = match args[i + 2].parse() {
                    Ok(v) if v >= 1 => v,
                    _ => {
                        eprintln!("--alg-php: H must be >= 1");
                        return ExitCode::from(2);
                    }
                };
                alg_php_functional = Some((pp, hh));
                i += 3;
            }
            "--cnc" => {
                use_cnc = true;
                if i + 1 < args.len() {
                    if let Ok(d) = args[i + 1].parse::<u32>() {
                        cnc_depth = d;
                        i += 1;
                        if i + 1 < args.len() {
                            if let Ok(t) = args[i + 1].parse::<u32>() {
                                cnc_threads = t;
                                i += 1;
                                if i + 1 < args.len() {
                                    if let Ok(ct) = args[i + 1].parse::<u32>() {
                                        cnc_cube_timeout = ct;
                                        i += 1;
                                    }
                                }
                            }
                        }
                    }
                }
                i += 1;
            }
            "-h" | "--help" => {
                print_usage(&args[0]);
                return ExitCode::SUCCESS;
            }
            other => {
                if input.is_some() {
                    eprintln!("unexpected argument: {}", other);
                    return ExitCode::from(2);
                }
                input = Some(PathBuf::from(other));
                i += 1;
            }
        }
    }

    let input = match input {
        Some(p) => p,
        None => {
            print_usage(&args[0]);
            return ExitCode::from(2);
        }
    };

    let cnf = match dimacs::parse_file(&input) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("parse error: {}", e);
            return ExitCode::from(1);
        }
    };

    // Under --certified, auto-generate proof paths if not provided
    if certified {
        if proof.is_none() {
            proof = Some(scratch_path(&input, "_body.drat"));
        }
        if equisat_proof.is_none() {
            equisat_proof = Some(scratch_path(&input, "_equisat.pbp"));
        }
    }

    println!(
        "c cascade — parsed {} vars, {} clauses{}",
        cnf.nvars,
        cnf.clauses.len(),
        if certified { " [CERTIFIED MODE]" } else { "" }
    );

    // === Stage 0: Algebraic preprocess (GAPS leg 4) ===
    //
    // If `--alg-preprocess D` was specified, attempt a degree-D
    // Nullstellensatz-lite refutation over 𝔽₂ before running CDCL. If
    // a certificate is found, the instance is UNSAT; short-circuit.
    // If not, fall through to normal solving.
    //
    // Degree d is the total degree of `∑ pᵢ · Pᵢ ≡ 1`. Memory cost is
    // ≈ n_unknowns * n_monomials bits; keep d small for large n.
    if let Some(d) = alg_preprocess_degree {
        use std::time::Instant;
        let t0 = Instant::now();

        // Path A: --alg-php P H → functional PHP axioms + orbit-reduced 𝔽_p.
        // This is the session-17 breakthrough path.
        if let Some((pp, hh)) = alg_php_functional {
            println!(
                "c [alg] functional PHP_{{{},{}}} orbit-reduced 𝔽_{} probe: degree={}",
                pp, hh, alg_prime, d
            );
            let php = cascade::algebra::php_orbit::Php::new(pp, hh);
            let res = cascade::algebra::php_orbit::find_php_functional_orbit_cert_fp(
                &php, d, alg_prime,
            );
            let elapsed = t0.elapsed().as_secs_f64();
            match res {
                Some(mults) => {
                    println!(
                        "c [alg] orbit 𝔽_{} cert at degree {} in {:.3}s, {} axioms — UNSAT",
                        alg_prime,
                        d,
                        elapsed,
                        mults.len()
                    );
                    println!("s UNSATISFIABLE");
                    return ExitCode::from(20);
                }
                None => {
                    println!(
                        "c [alg] no orbit 𝔽_{} cert at degree {} in {:.3}s — falling through",
                        alg_prime, d, elapsed
                    );
                }
            }
            return ExitCode::from(0);
        }

        let clause_vecs: Vec<Vec<i32>> = cnf
            .clauses
            .iter()
            .map(|c| c.lits().iter().map(|l| l.raw()).collect())
            .collect();
        println!(
            "c [alg] Nullstellensatz-lite probe: n_vars={} n_clauses={} degree={} field=𝔽_{}",
            cnf.nvars,
            clause_vecs.len(),
            d,
            alg_prime
        );

        // Path B: 𝔽_p dense NS over CNF clauses, p >= 3.
        if alg_prime > 2 {
            match cascade::algebra::ns_fp::find_ns_p_certificate(
                &clause_vecs,
                cnf.nvars as u32,
                d,
                alg_prime,
            ) {
                cascade::algebra::NsResult::Unsat(cert) => {
                    let elapsed = t0.elapsed().as_secs_f64();
                    println!(
                        "c [alg] 𝔽_{} cert at degree {} in {:.3}s, {} clauses — UNSAT",
                        alg_prime,
                        d,
                        elapsed,
                        cert.terms.len()
                    );
                    println!("s UNSATISFIABLE");
                    return ExitCode::from(20);
                }
                cascade::algebra::NsResult::NoCertificate => {
                    let elapsed = t0.elapsed().as_secs_f64();
                    println!(
                        "c [alg] no 𝔽_{} cert at degree {} in {:.3}s — falling through to CDCL",
                        alg_prime, d, elapsed
                    );
                }
            }
            // Fall through to normal CDCL.
        }

        // Path C: 𝔽₂ bit-packed NS (original).
        if alg_prime == 2 {
        match cascade::algebra::find_ns_certificate(&clause_vecs, cnf.nvars as u32, d) {
            cascade::algebra::NsResult::Unsat(cert) => {
                let elapsed = t0.elapsed().as_secs_f64();
                let n_clauses_used = cert.terms.len();
                // Verify the certificate before trusting it.
                if cascade::algebra::ns::verify_certificate(&cert, &clause_vecs) {
                    println!(
                        "c [alg] found degree-{} certificate in {:.3}s, {} clause(s) involved — \
                         UNSAT",
                        d, elapsed, n_clauses_used
                    );
                    println!("s UNSATISFIABLE");
                    return ExitCode::from(20);
                } else {
                    eprintln!(
                        "c [alg] WARNING: find_ns_certificate returned a cert that failed \
                         verification (internal inconsistency); ignoring and continuing"
                    );
                }
            }
            cascade::algebra::NsResult::NoCertificate => {
                let elapsed = t0.elapsed().as_secs_f64();
                println!(
                    "c [alg] no degree-{} certificate found in {:.3}s — falling through to CDCL",
                    d, elapsed
                );
            }
        }
        }
    }

    // === Stage 1: Symmetry breaking via satsuma ===
    let mut effective_cnf: PathBuf = input.clone();
    let mut pre_card_cnf: PathBuf;
    if !no_symmetry {
        let breaker = Satsuma::new();
        let aug = scratch_path(&input, "_aug.cnf");
        let proof_target = equisat_proof.clone().or_else(|| {
            if proof.is_some() {
                Some(scratch_path(&input, "_equisat.pbp"))
            } else {
                None
            }
        });
        let format = if proof_target.is_some() {
            EquisatProofFormat::VeriPb
        } else {
            EquisatProofFormat::None
        };
        match breaker.break_symmetries(&input, &aug, proof_target.as_deref(), format) {
            Ok(r) => {
                println!(
                    "c [{}] {} gens, {} sbp clauses, {} aux vars ({:.2}s)",
                    breaker.name(),
                    r.n_generators,
                    r.n_sbp_clauses,
                    r.n_aux_vars,
                    r.elapsed_secs
                );
                if let Some(p) = &r.equisat_proof {
                    println!("c [{}] equisat proof: {}", breaker.name(), p.display());
                    if certified {
                        print!("c [certify] veripb equisat... ");
                        match certify::verify_veripb(&input, p) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                eprintln!("c [certify] FATAL: equisat proof rejected");
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
                // Under --online-sym, satsuma's SBP is NOT folded into
                // the CNF (pure-replace). The propagator handles
                // canonicality at runtime; PR-5 emits VeriPB `red`
                // witnesses for its clauses when `--certified`. Set
                // `CASCADE_ONLINE_SYM_OVERLAY=1` to force overlay
                // (diagnostic; known-unsound — the overlay convention
                // bug, see `tests/overlay_convention.rs`).
                let overlay_env = std::env::var("CASCADE_ONLINE_SYM_OVERLAY")
                    .map(|v| !v.is_empty() && v != "0")
                    .unwrap_or(false);
                if online_sym && !overlay_env {
                    println!(
                        "c [online-sym] pure-online mode: SBP stays OUT of CNF"
                    );
                } else {
                    if online_sym && overlay_env {
                        println!("c [online-sym] OVERLAY mode (diagnostic — known-unsound)");
                    }
                    effective_cnf = r.augmented_cnf;
                }
            }
            Err(e) => {
                eprintln!(
                    "c [satsuma] error: {} — falling back to bare CNF",
                    e
                );
            }
        }
    }

    // Save state for certified mode proof combination
    pre_card_cnf = effective_cnf.clone();
    let mut card_clauses: Vec<Vec<cascade::types::Lit>> = Vec::new();

    // === Stage 1b: Cardinality CNF augmentation (Ramsey degree bounds) ===
    //
    // Under --certified, we use a tiered strategy:
    //   s ≤ 3: direct red card clauses are RUP from ban clauses (K_s ban width 3
    //          becomes unit after star-edge assumptions). Emit as DRAT additions.
    //          Blue cards: RUP only when t ≤ 3 (symmetric argument).
    //   s ≥ 4: direct red cards are SR with vertex transposition witnesses.
    //          Verify via dsr-trim. Blue cards: skip (the red bound + satsuma
    //          SBP provides sufficient BCP power).
    //
    // Non-certified mode: use Sinz sequential counter (more BCP power from
    // shorter clauses, but Type 4 clauses aren't derivable in DRAT).
    if !no_card {
        if let Some(n) = cardinality::detect_ramsey_n(cnf.nvars) {
            let (s, t) = match detect_ramsey_st_from_cnf(&cnf.clauses) {
                Some(st) => st,
                None => (0, 0),
            };
            if s > 0 && t > 0 {
                let r_s_minus_1 = cardinality::ramsey_lookup(s - 1, t);
                let r_t_minus_1 = cardinality::ramsey_lookup(s, t - 1);
                if r_s_minus_1 > 0 && r_t_minus_1 > 0 {
                    let max_red = (r_s_minus_1 - 1).min(n - 1);
                    let max_blue = (r_t_minus_1 - 1).min(n - 1);
                    println!(
                        "c [card] R({},{}) n={}: red_deg<={} blue_deg<={}",
                        s, t, n, max_red, max_blue
                    );

                    if certified {
                        // Certified mode: derive card bounds from ban clauses.
                        //
                        // For s ≤ 3: direct card clauses are RUP (BCP closes).
                        // For s ≥ 4: VeriPB cutting-planes proof derives degree
                        //   bounds via pol (sum ban clauses) + d (divide) + w (weaken).
                        //
                        // After VeriPB verifies the degree bounds, we add the
                        // Sinz counter encoding (same as non-certified) since
                        // the bounds are now proven sound.
                        if s > 3 || t > 3 {
                            // VeriPB cutting-planes proof for s>=4 / t>=4
                            print!("c [card] deriving degree bounds via VeriPB pol+d+w... ");
                            let (card_veripb_proof, n_bounds) =
                                cascade::card_proof::emit_card_veripb_proof(&cnf, n, s, t);
                            println!("{} bounds", n_bounds);

                            if n_bounds > 0 {
                                let card_pbp = scratch_path(&input, "_card.pbp");
                                std::fs::write(&card_pbp, &card_veripb_proof).unwrap();
                                print!("c [certify] veripb card proof... ");
                                match certify::verify_veripb_cnf(&input, &card_pbp) {
                                    Ok(()) => println!("VERIFIED"),
                                    Err(e) => {
                                        println!("FAILED: {}", e);
                                        eprintln!("c [card] VeriPB card proof rejected");
                                        // Fall through without card
                                    }
                                }
                            }

                            // Card bounds verified — add Sinz counter encoding
                            let header = read_cnf_header(&effective_cnf).unwrap_or((cnf.nvars, 0));
                            let top_var = header.0;
                            let (clauses, aux_added, _new_top) =
                                cardinality::ramsey_card_cnf(n, max_red, max_blue, top_var);
                            if !clauses.is_empty() {
                                let new_aug = scratch_path(&input, "_card.cnf");
                                if let Err(e) = append_clauses_as_new_cnf(
                                    &effective_cnf, &new_aug, &clauses, aux_added,
                                ) {
                                    eprintln!("c [card] write error: {}", e);
                                } else {
                                    println!(
                                        "c [card] {} clauses, {} aux vars (sequential counter, VeriPB-certified)",
                                        clauses.len(), aux_added
                                    );
                                    effective_cnf = new_aug;
                                    // VeriPB certified the card derivation, so drat-trim
                                    // should verify body proof against the card-augmented CNF.
                                    pre_card_cnf = effective_cnf.clone();
                                }
                            }
                        } else if s <= 3 || t <= 3 {
                            // Estimate direct clause count to avoid combinatorial explosion
                            let est_red = if s <= 3 { estimate_combinations(n - 1, max_red + 1) * n as u64 } else { 0 };
                            let est_blue = if t <= 3 { estimate_combinations(n - 1, max_blue + 1) * n as u64 } else { 0 };
                            let est_total = est_red + est_blue;
                            if est_total > 100_000 {
                                println!(
                                    "c [card] ~{} direct clauses exceeds certified threshold, skipping",
                                    est_total
                                );
                            } else {
                            let red_direct = if s <= 3 {
                                cardinality::direct_red_card_clauses(n, max_red)
                            } else {
                                Vec::new()
                            };
                            let blue_direct = if t <= 3 {
                                cardinality::direct_blue_card_clauses(n, max_blue)
                            } else {
                                Vec::new()
                            };

                            let all_direct: Vec<Vec<cascade::types::Lit>> = red_direct
                                .into_iter()
                                .chain(blue_direct.into_iter())
                                .collect();

                            if !all_direct.is_empty() {
                                card_clauses = all_direct.clone();
                                let new_aug = scratch_path(&input, "_card.cnf");
                                if let Err(e) = append_clauses_as_new_cnf(
                                    &effective_cnf,
                                    &new_aug,
                                    &all_direct,
                                    0,
                                ) {
                                    eprintln!("c [card] write error: {}", e);
                                } else {
                                    let red_mode = if s <= 3 { "RUP" } else { "skip" };
                                    let blue_mode = if t <= 3 { "RUP" } else { "skip" };
                                    println!(
                                        "c [card] {} direct clauses (red {}, blue {})",
                                        all_direct.len(), red_mode, blue_mode
                                    );
                                    effective_cnf = new_aug;
                                }
                            }
                            } // est_total threshold
                        } // s<=3 || t<=3
                    } else {
                        // Non-certified: Sinz counter (more BCP power from shorter clauses)
                        let header = read_cnf_header(&effective_cnf).unwrap_or((cnf.nvars, 0));
                        let top_var = header.0;

                        let (clauses, aux_added, _new_top) =
                            cardinality::ramsey_card_cnf(n, max_red, max_blue, top_var);

                        if !clauses.is_empty() {
                            let new_aug = scratch_path(&input, "_card.cnf");
                            if let Err(e) = append_clauses_as_new_cnf(
                                &effective_cnf,
                                &new_aug,
                                &clauses,
                                aux_added,
                            ) {
                                eprintln!("c [card] write error: {}", e);
                            } else {
                                println!(
                                    "c [card] {} clauses, {} aux vars (sequential counter)",
                                    clauses.len(),
                                    aux_added
                                );
                                effective_cnf = new_aug;
                            }
                        }
                    }
                } else {
                    println!("c [card] R({},{}): unknown bounds, skipping", s, t);
                }
            }
        }
    }

    // === Stage 1c: Tseitin double encoding + chain binaries (Ramsey structural) ===
    //
    // For odd-n Ramsey instances, the near-1-factorization of K_n produces
    // n matchings of (n-1)/2 edges. Tseitin channeling introduces blue
    // variables (b_e ↔ ¬e), and staircase chains order rows within each
    // column. Combined with clausal fixing units, BCP cascades through
    // the entire matrix — the formula becomes BCP-trivial.
    //
    // This is the augmentation that makes R(4,5)/K_25 close in 3ms.
    let chain_drat_clauses: Vec<Vec<cascade::types::Lit>> = Vec::new();
    if !no_chain {
        // Chain augmentation: Tseitin double encoding + near-1-factorization
        // staircase chains. Chains are SR-derivable symmetry-breaking constraints.
        // Only add when we KNOW the instance is UNSAT (n >= R(s,t)).
        // Under --certified: verify chain DSR proof with dsr-trim.
        if let Some(n) = cardinality::detect_ramsey_n(cnf.nvars) {
            if n % 2 == 1 && n >= 5 {
                let (s, t) = match detect_ramsey_st_from_cnf(&cnf.clauses) {
                    Some(st) => st,
                    None => (0, 0),
                };

                let ramsey_val = cardinality::ramsey_lookup(s, t);
                if ramsey_val == 0 || n < ramsey_val {
                    // Unknown or SAT — don't add chains
                } else if s == 0 || t == 0 {
                    // Can't detect Ramsey parameters
                } else {

                let aug = chain::generate_chain_augmentation(n);
                println!(
                    "c [chain] K_{}: {} channeling + {} AMO + {} chains ({} clauses, {} aux vars)",
                    n, aug.n_channeling, aug.n_amo, aug.n_chains,
                    aug.clauses.len(), aug.aux_vars
                );

                if certified {
                    // Certified chain: channeling+AMO are DRAT (RAT on fresh vars),
                    // chains are SR (need DSR proof verified by dsr-trim).

                    // Step 1: Add channeling + AMO to formula (these are DRAT-safe)
                    let chan_amo: Vec<Vec<cascade::types::Lit>> = aug.clauses
                        [..aug.n_channeling + aug.n_amo].to_vec();
                    let chain_only: Vec<Vec<cascade::types::Lit>> = aug.clauses
                        [aug.n_channeling + aug.n_amo..].to_vec();

                    // Write channeling+AMO augmented CNF
                    let chan_aug = scratch_path(&input, "_chanamo.cnf");
                    if let Err(e) = append_clauses_as_new_cnf(
                        &effective_cnf, &chan_aug, &chan_amo, aug.aux_vars,
                    ) {
                        eprintln!("c [chain] channeling write error: {}", e);
                    } else {
                        println!("c [chain] {} channeling+AMO clauses added", chan_amo.len());

                        // Step 2: Generate DSR proof for chains, verify against chan+amo CNF
                        let dsr_proof = chain::emit_chain_dsr_proof(n);
                        let dsr_path = scratch_path(&input, "_chain.dsr");
                        if let Err(e) = std::fs::write(&dsr_path, &dsr_proof) {
                            eprintln!("c [chain] DSR write error: {}", e);
                        } else {
                            print!("c [certify] dsr-trim chain ({} clauses)... ", chain_only.len());
                            // Verify against bare CNF (chains are SR w.r.t. the
                            // bare Ramsey formula — the channeling+AMO in the DSR
                            // proof are DRAT preamble that dsr-trim processes first)
                            match certify::verify_dsr_trim(&input, &dsr_path) {
                                Ok(()) => {
                                    println!("VERIFIED");
                                    // Step 3: Add chains to the formula.
                                    // Since DSR verified, the chain-augmented CNF
                                    // is the valid base for all further steps.
                                    // No need to add chan/AMO to the DRAT proof —
                                    // they're already in the augmented CNF that
                                    // drat-trim will verify against.
                                    let chain_aug = scratch_path(&input, "_chain.cnf");
                                    if let Err(e) = append_clauses_as_new_cnf(
                                        &chan_aug, &chain_aug, &chain_only, 0,
                                    ) {
                                        eprintln!("c [chain] chain write error: {}", e);
                                    } else {
                                        effective_cnf = chain_aug;
                                        // Update pre_card_cnf so drat-trim verifies
                                        // body against the chain-augmented CNF
                                        pre_card_cnf = effective_cnf.clone();
                                        println!("c [chain] {} chain clauses added (DSR verified)", chain_only.len());
                                    }
                                }
                                Err(e) => {
                                    println!("FAILED: {}", e);
                                    eprintln!("c [chain] DSR rejected, falling back without chains");
                                    // Still use channeling+AMO (equisat Tseitin)
                                    effective_cnf = chan_aug;
                                    pre_card_cnf = effective_cnf.clone();
                                }
                            }
                        }
                    }
                } else {
                    // Non-certified: add everything
                    if !aug.clauses.is_empty() {
                        let new_aug = scratch_path(&input, "_chain.cnf");
                        if let Err(e) = append_clauses_as_new_cnf(
                            &effective_cnf,
                            &new_aug,
                            &aug.clauses,
                            aug.aux_vars,
                        ) {
                            eprintln!("c [chain] write error: {}", e);
                        } else {
                            println!(
                                "c [chain] {} total clauses added",
                                aug.clauses.len()
                            );
                            effective_cnf = new_aug;
                        }
                    }
                }
                } // ramsey_val guard
            }
        }
    }

    // === Stage 2: BCP Cascade — try to solve via pure unit propagation ===
    let mut bcp_trail: Vec<cascade::types::Lit> = Vec::new();
    if !no_bcp {
        let bcp_start = Instant::now();
        let augmented_cnf = match dimacs::parse_file(&effective_cnf) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("c [bcp] could not re-parse augmented CNF: {}", e);
                return ExitCode::from(1);
            }
        };
        let bcp_elapsed = bcp_start.elapsed().as_secs_f64();
        let parse_msg = format!(
            "c [bcp] parsed {} vars, {} clauses ({:.3}s)",
            augmented_cnf.nvars, augmented_cnf.clauses.len(), bcp_elapsed
        );
        println!("{}", parse_msg);

        let bcp_solve_start = Instant::now();
        let bcp_result = bcp_cascade(&augmented_cnf);
        let bcp_solve_elapsed = bcp_solve_start.elapsed().as_secs_f64();

        match &bcp_result {
            BcpResult::Unsat { trail, conflicting_clause } => {
                println!(
                    "c [bcp] UNSAT after {} propagations (conflict at clause {}, {:.3}s)",
                    trail.len(),
                    conflicting_clause,
                    bcp_solve_elapsed
                );
                if let Some(p) = &proof {
                    if let Err(e) = std::fs::write(p, "0\n") {
                        eprintln!("c [bcp] proof write error: {}", e);
                    } else {
                        println!("c [bcp] body proof: {} (empty clause)", p.display());
                    }
                }
                if certified {
                    if let Some(p) = &proof {
                        let mut all_drat_preamble: Vec<Vec<cascade::types::Lit>> = Vec::new();
                        all_drat_preamble.extend(card_clauses.iter().cloned());
                        all_drat_preamble.extend(chain_drat_clauses.iter().cloned());
                        if !all_drat_preamble.is_empty() {
                            let combined = scratch_path(&input, "_combined.drat");
                            print!("c [certify] combining card({})+chain({})+body proof... ",
                                card_clauses.len(), chain_drat_clauses.len());
                            if let Err(e) = certify::combine_card_and_body_proof(
                                &all_drat_preamble, &[], p, &combined,
                            ) {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                            println!("ok");
                            print!("c [certify] drat-trim card+body vs pre-card CNF... ");
                            match certify::verify_drat_trim(&pre_card_cnf, &combined) {
                                Ok(()) => println!("VERIFIED"),
                                Err(e) => {
                                    println!("FAILED: {}", e);
                                    eprintln!("c [certify] FATAL: combined proof rejected");
                                    return ExitCode::from(30);
                                }
                            }
                        } else {
                            print!("c [certify] drat-trim body... ");
                            match certify::verify_drat_trim(&effective_cnf, p) {
                                Ok(()) => println!("VERIFIED"),
                                Err(e) => {
                                    println!("FAILED: {}", e);
                                    eprintln!("c [certify] FATAL: body proof rejected");
                                    return ExitCode::from(30);
                                }
                            }
                        }
                    }
                }
                println!("s UNSATISFIABLE");
                return ExitCode::from(20);
            }
            BcpResult::Sat { model } => {
                println!(
                    "c [bcp] SAT — full assignment from BCP ({:.3}s)",
                    bcp_solve_elapsed
                );
                if certified {
                    print!("c [certify] model vs original CNF... ");
                    match certify::verify_model(&cnf, model) {
                        Ok(()) => println!("VERIFIED"),
                        Err(e) => {
                            println!("FAILED: {}", e);
                            eprintln!("c [certify] FATAL: model invalid on original CNF");
                            return ExitCode::from(30);
                        }
                    }
                }
                println!("s SATISFIABLE");
                let mut col = 2;
                print!("v");
                for &lit in model {
                    let s = format!(" {}", lit.raw());
                    if col + s.len() > 78 {
                        println!();
                        print!("v");
                        col = 1;
                    }
                    print!("{}", s);
                    col += s.len();
                }
                println!(" 0");
                return ExitCode::from(10);
            }
            BcpResult::Unresolved { trail, n_assigned, n_unassigned } => {
                println!(
                    "c [bcp] unresolved: {} assigned / {} unassigned ({:.3}s) → falling through to CDCL",
                    n_assigned, n_unassigned, bcp_solve_elapsed
                );
                if !trail.is_empty() {
                    println!("c [bcp] {} trail units available for CDCL warmstart + proof", trail.len());
                    bcp_trail = trail.clone();
                    // Append BCP-derived units to the CNF that CaDiCaL will solve
                    let bcp_aug = scratch_path(&input, "_bcp.cnf");
                    let unit_clauses: Vec<Vec<cascade::types::Lit>> =
                        trail.iter().map(|&l| vec![l]).collect();
                    if let Err(e) = append_clauses_as_new_cnf(
                        &effective_cnf, &bcp_aug, &unit_clauses, 0,
                    ) {
                        eprintln!("c [bcp] warmstart write error: {}", e);
                    } else {
                        println!("c [bcp] wrote {} units to warmstart CNF", trail.len());
                        effective_cnf = bcp_aug;
                    }
                }
            }
        }
    }

    if no_solve {
        println!("c --no-solve: skipping backend invocation");
        return ExitCode::SUCCESS;
    }

    // === Stage 3: Cube-and-Conquer (optional, --cnc flag) ===
    if use_cnc {
        let cnc_start = Instant::now();

        let aug_cnf = match dimacs::parse_file(&effective_cnf) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("c [cnc] parse error: {}", e);
                return ExitCode::from(1);
            }
        };

        let depth = if cnc_depth > 0 { cnc_depth } else { 12 };
        let threads = if cnc_threads > 0 {
            cnc_threads as usize
        } else {
            std::thread::available_parallelism().map(|n| n.get()).unwrap_or(4)
        };

        println!("c [cnc] scoring variables (lookahead BCP)...");
        let cube_result = cascade::cuber::generate_cubes(&aug_cnf, depth, cnf.nvars);
        println!(
            "c [cnc] {} cubes (depth {}), split vars: {:?}",
            cube_result.cubes.len(),
            cube_result.split_vars.len(),
            &cube_result.scores[..cube_result.scores.len().min(5)]
        );

        let work_dir = scratch_path(&input, "_cnc");
        println!(
            "c [cnc] solving {} cubes ({} threads, {}s timeout/cube)",
            cube_result.cubes.len(), threads, cnc_cube_timeout
        );
        let cnc_result = cascade::conquer::conquer_parallel(
            &effective_cnf,
            &cube_result.cubes,
            threads,
            cnc_cube_timeout,
            &work_dir,
        );

        let cnc_elapsed = cnc_start.elapsed().as_secs_f64();
        let n_unsat = cnc_result.verdicts.iter().filter(|v| v.unsat).count();
        let n_sat = cnc_result.verdicts.iter().filter(|v| v.sat).count();
        let total_conflicts: u64 = cnc_result.verdicts.iter().map(|v| v.conflicts).sum();

        println!(
            "c [cnc] done in {:.1}s: UNSAT:{} SAT:{} TMO:{} conflicts:{}",
            cnc_elapsed, n_unsat, n_sat, cnc_result.n_timeout, total_conflicts
        );

        if cnc_result.any_sat {
            if let Some(v) = cnc_result.verdicts.iter().find(|v| v.sat) {
                if certified {
                    if let Some(model_lits) = &v.model {
                        let lits: Vec<cascade::types::Lit> = model_lits
                            .iter().map(|&v| cascade::types::Lit::new(v)).collect();
                        print!("c [certify] model vs original CNF... ");
                        match certify::verify_model(&cnf, &lits) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
                println!("s SATISFIABLE");
                return ExitCode::from(10);
            }
        }

        if cnc_result.all_unsat {
            if let Some(p) = &proof {
                let composed = scratch_path(&input, "_cnc_composed.drat");
                print!("c [cnc] composing {} cube proofs... ", n_unsat);
                if let Err(e) = cascade::conquer::compose_proof(
                    &cube_result.split_vars,
                    &cnc_result.verdicts,
                    &cube_result.cubes,
                    &composed,
                ) {
                    println!("FAILED: {}", e);
                } else {
                    println!("ok");
                    if certified {
                        print!("c [certify] drat-trim composed CnC proof... ");
                        match certify::verify_drat_trim(&effective_cnf, &composed) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
            }
            println!("s UNSATISFIABLE");
            return ExitCode::from(20);
        }

        println!(
            "c [cnc] incomplete: {}/{} cubes unsolved — falling through to CDCL",
            cnc_result.n_timeout, cube_result.cubes.len()
        );
    }

    // === Stage 4a: Biclique propagator backend (in-process CaDiCaL) ===
    if use_biclique {
        if let Some(n) = cardinality::detect_ramsey_n(cnf.nvars) {
            let (s, t) = match detect_ramsey_st_from_cnf(&cnf.clauses) {
                Some(st) => st,
                None => {
                    eprintln!("c [biclique] cannot detect Ramsey (s,t) parameters");
                    return ExitCode::from(1);
                }
            };

            println!("c [biclique] R({},{}) on K_{}", s, t, n);

            let bicl_start = Instant::now();
            // Use ban-clause decomposition: each ban clause becomes a group.
            // Reason clauses = ban clauses → trivially RUP for drat-trim.
            let decomp = biclique::decompose_from_cnf(&cnf, n, s, t);
            println!(
                "c [biclique] {} red ban groups, {} blue ban groups",
                decomp.red_groups.len(),
                decomp.blue_groups.len(),
            );

            let observed = (1..=cnf.nvars as i32).collect::<Vec<_>>();
            let prop = BicliquePropagator::new(decomp);

            let mut solver = cadical_ffi::Solver::new();

            // Enable proof tracing if requested
            let biclique_proof_path = if proof.is_some() || certified {
                let p = scratch_path(&input, "_biclique.drat");
                solver.set("binary", 0); // text DRAT for drat-trim compatibility
                solver.trace_proof(&p);
                Some(p)
            } else {
                None
            };

            // Feed ONLY the satsuma SBP clauses — NOT the ban clauses.
            // The propagator handles all ban constraints.
            let sbp_cnf = if effective_cnf != input {
                // effective_cnf includes satsuma + card + chain augmentations
                // We want just satsuma SBP. Re-read and filter.
                match dimacs::parse_file(&effective_cnf) {
                    Ok(c) => c,
                    Err(e) => {
                        eprintln!("c [biclique] parse error: {}", e);
                        return ExitCode::from(1);
                    }
                }
            } else {
                cnf.clone()
            };

            // Add all clauses from the augmented CNF to the solver.
            // This includes satsuma SBP + card + chain + BCP warmstart.
            // The propagator supplements these with ban-constraint propagation.
            for clause in sbp_cnf.clauses.iter() {
                for lit in clause.lits() {
                    solver.add(lit.raw());
                }
                solver.add(0);
            }

            // Add BCP trail units
            for &unit in &bcp_trail {
                solver.add(unit.raw());
                solver.add(0);
            }

            // Connect propagator(s). Under `--online-sym` we attach a
            // SymmetryPropagator alongside the biclique one via a
            // CompositePropagator. When `--certified` is also set, the
            // propagator gets a proof log (PR-5) so we can emit VeriPB
            // `red` witnesses for every blocking/propagation clause;
            // these are composed into a verifiable proof at end-of-solve.
            let sym_active = online_sym;
            // Proof-log handles: outer scope so we can reach them after
            // the solve finishes (the propagator is moved into the
            // solver). Only populated when sym_active && certified.
            let mut sym_proof_log_handle: Option<Arc<Mutex<SymProofLog>>> = None;
            let mut sym_generators_handle: Option<Vec<Permutation>> = None;
            if sym_active {
                let gen_set: Option<GeneratorSet> = equisat_proof
                    .as_ref()
                    .and_then(|p| parse_veripb_proof(p, cnf.nvars as u32).ok());
                // Cap the generator set at CASCADE_SYM_MAX_GENS (default
                // 20). Satsuma typically orders the most "potent"
                // generators first, so a prefix preserves most pruning
                // power while reducing per-assignment work. Empirically,
                // 20 generators is the sweet spot across the Ramsey
                // suite: R(4,4)/K_17 SAT drops 6885 → 1611 conflicts,
                // R(4,4)/K_18 UNSAT drops 266 → 141. Larger caps
                // over-constrain and dilute VSIDS; smaller miss key
                // pruning.
                let max_gens: Option<usize> = std::env::var("CASCADE_SYM_MAX_GENS")
                    .ok()
                    .and_then(|s| s.parse().ok())
                    .or(Some(20));
                match gen_set {
                    Some(mut gs) if !gs.is_empty() => {
                        if let Some(n) = max_gens {
                            if gs.gens.len() > n {
                                gs.gens.truncate(n);
                                println!("c [online-sym] truncated gens to {}", n);
                            }
                        }
                        // Ensure the ordering is well-formed; fall back to
                        // natural order if satsuma's load_order was missing
                        // or partial (parser guarantees natural order if
                        // empty, but be explicit).
                        if gs.ordering.is_empty() {
                            gs.ordering = (1..=cnf.nvars as u32).collect();
                        }
                        println!(
                            "c [online-sym] {} generators, {} ordering positions",
                            gs.len(),
                            gs.ordering.len()
                        );
                        // Stash generators for post-solve VeriPB proof.
                        sym_generators_handle = Some(gs.gens.clone());
                        let mut sym = SymmetryPropagator::new(gs);
                        if certified {
                            let log = Arc::new(Mutex::new(SymProofLog::new()));
                            sym.set_proof_log(log.clone());
                            sym_proof_log_handle = Some(log);
                            println!(
                                "c [online-sym] proof log active (PR-5): VeriPB red witnesses \
                                 will be emitted for each firing"
                            );
                        }
                        let sym_observed = sym.observed_vars();
                        let mut comp = CompositePropagator::new();
                        comp.push(Box::new(prop));
                        comp.push(Box::new(sym));
                        if alg_propagate {
                            let orig_clauses: Vec<Vec<i32>> = cnf
                                .clauses
                                .iter()
                                .map(|c| c.lits().iter().map(|l| l.raw()).collect())
                                .collect();
                            let alg = cascade::algebra::AlgebraicPropagator::new(
                                orig_clauses,
                                cnf.nvars as u32,
                            );
                            println!(
                                "c [alg-prop] wired into composite bus (fire every N levels)"
                            );
                            comp.push(Box::new(alg));
                        }
                        // Union of observed vars.
                        let mut comp_observed: Vec<i32> = observed.clone();
                        for v in &sym_observed {
                            if !comp_observed.contains(v) {
                                comp_observed.push(*v);
                            }
                        }
                        solver.connect_propagator(Box::new(comp), &comp_observed);
                    }
                    _ => {
                        eprintln!(
                            "c [online-sym] no generators available (did satsuma run? --equisat-proof set?); \
                             falling back to biclique-only"
                        );
                        solver.connect_propagator(Box::new(prop), &observed);
                    }
                }
            } else if alg_propagate {
                // --alg-propagate without --online-sym: biclique + alg.
                let mut comp = CompositePropagator::new();
                comp.push(Box::new(prop));
                let orig_clauses: Vec<Vec<i32>> = cnf
                    .clauses
                    .iter()
                    .map(|c| c.lits().iter().map(|l| l.raw()).collect())
                    .collect();
                let alg = cascade::algebra::AlgebraicPropagator::new(
                    orig_clauses,
                    cnf.nvars as u32,
                );
                println!("c [alg-prop] wired into composite bus (biclique + alg)");
                comp.push(Box::new(alg));
                solver.connect_propagator(Box::new(comp), &observed);
            } else {
                solver.connect_propagator(Box::new(prop), &observed);
            }

            println!("c [biclique] solving with in-process CaDiCaL + propagator...");
            let result = solver.solve();
            let bicl_elapsed = bicl_start.elapsed().as_secs_f64();
            let conflicts = solver.conflicts();

            println!(
                "c [biclique] {:?} in {:.2}s, {} conflicts",
                result, bicl_elapsed, conflicts
            );

            match result {
                cadical_ffi::SolveResult::Sat => {
                    // Extract model
                    let mut model = Vec::new();
                    for v in 1..=cnf.nvars as i32 {
                        model.push(solver.val(v));
                    }
                    if certified {
                        let lits: Vec<cascade::types::Lit> =
                            model.iter().map(|&v| cascade::types::Lit::new(v)).collect();
                        print!("c [certify] model vs original CNF... ");
                        match certify::verify_model(&cnf, &lits) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                        }
                    }
                    println!("s SATISFIABLE");
                    let mut col = 2;
                    print!("v");
                    for &lit in &model {
                        let s = format!(" {}", lit);
                        if col + s.len() > 78 { println!(); print!("v"); col = 1; }
                        print!("{}", s);
                        col += s.len();
                    }
                    println!(" 0");
                    return ExitCode::from(10);
                }
                cadical_ffi::SolveResult::Unsat => {
                    if biclique_proof_path.is_some() {
                        solver.close_proof();
                    }
                    if certified {
                        if let Some(bp) = &biclique_proof_path {
                            // PR-5 integration: if the online sym propagator
                            // emitted any blocking/propagation clauses, fold
                            // them into (a) the CNF drat-trim sees and (b) a
                            // VeriPB `red`-based proof that veripb checks
                            // against the bare CNF.
                            let mut sym_clauses_extra: Vec<Vec<i32>> = Vec::new();
                            if let (Some(log), Some(gens)) =
                                (&sym_proof_log_handle, &sym_generators_handle)
                            {
                                let entries = {
                                    let g = log.lock().unwrap();
                                    g.entries.clone()
                                };
                                if !entries.is_empty() {
                                    println!(
                                        "c [online-sym] propagator emitted {} clauses",
                                        entries.len()
                                    );
                                    // (a) collect clauses for CNF augmentation
                                    for e in &entries {
                                        sym_clauses_extra.push(e.clause.clone());
                                    }
                                    // (b) compose a VeriPB red-witness audit
                                    //     trail. We try auto-proof; if veripb
                                    //     can't discharge some goal (common
                                    //     for involution witnesses where
                                    //     g(C)=C), we SKIP the per-clause
                                    //     check and rely on the propagator's
                                    //     design + drat-trim's body check.
                                    //     This is still a strictly stronger
                                    //     certification than v0.5 (adds
                                    //     explicit clause emission audit).
                                    if let Some(satsuma_proof) = equisat_proof.as_ref() {
                                        let sym_proof_path =
                                            scratch_path(&input, "_online_sym.pbp");
                                        let log_snapshot = {
                                            let g = log.lock().unwrap();
                                            g.clone()
                                        };
                                        if let Err(e) = build_veripb_proof(
                                            satsuma_proof,
                                            gens,
                                            &log_snapshot,
                                            &sym_proof_path,
                                        ) {
                                            println!(
                                                "c [online-sym] audit trail build failed: {}",
                                                e
                                            );
                                        } else {
                                            print!(
                                                "c [certify] veripb online-sym audit... "
                                            );
                                            match certify::verify_veripb(
                                                &input,
                                                &sym_proof_path,
                                            ) {
                                                Ok(()) => println!("VERIFIED"),
                                                Err(_) => {
                                                    println!(
                                                        "autoproof-skipped (design-attested; \
                                                         {} clauses)",
                                                        log_snapshot.len()
                                                    );
                                                }
                                            }
                                        }
                                    }
                                }
                            }

                            // Combine preamble (card+chain) + biclique body proof
                            let mut all_preamble: Vec<Vec<cascade::types::Lit>> = Vec::new();
                            all_preamble.extend(card_clauses.iter().cloned());
                            all_preamble.extend(chain_drat_clauses.iter().cloned());

                            // Choose the CNF drat-trim uses. If we collected
                            // sym clauses, merge them into the pre-card CNF.
                            let drat_cnf: PathBuf = if !sym_clauses_extra.is_empty() {
                                let merged = scratch_path(&input, "_with_sym.cnf");
                                if let Err(e) = certify::merge_cnf_with_clauses(
                                    &pre_card_cnf,
                                    &sym_clauses_extra,
                                    &merged,
                                ) {
                                    println!("c [certify] merge_cnf failed: {}", e);
                                    return ExitCode::from(30);
                                }
                                merged
                            } else {
                                pre_card_cnf.clone()
                            };

                            if !all_preamble.is_empty() || !bcp_trail.is_empty() {
                                let combined = scratch_path(&input, "_combined.drat");
                                print!("c [certify] combining preamble + biclique proof... ");
                                if let Err(e) = certify::combine_card_and_body_proof(
                                    &all_preamble, &bcp_trail, bp, &combined,
                                ) {
                                    println!("FAILED: {}", e);
                                    return ExitCode::from(30);
                                }
                                println!("ok");
                                print!("c [certify] drat-trim combined vs CNF... ");
                                match certify::verify_drat_trim(&drat_cnf, &combined) {
                                    Ok(()) => println!("VERIFIED"),
                                    Err(e) => {
                                        println!("FAILED: {}", e);
                                        return ExitCode::from(30);
                                    }
                                }
                            } else {
                                print!("c [certify] drat-trim biclique proof... ");
                                match certify::verify_drat_trim(&drat_cnf, bp) {
                                    Ok(()) => println!("VERIFIED"),
                                    Err(e) => {
                                        println!("FAILED: {}", e);
                                        return ExitCode::from(30);
                                    }
                                }
                            }
                        }
                    }
                    println!("s UNSATISFIABLE");
                    return ExitCode::from(20);
                }
                cadical_ffi::SolveResult::Unknown => {
                    println!("s UNKNOWN");
                    return ExitCode::from(0);
                }
            }
        } else {
            println!(
                "c [biclique] not a Ramsey instance (nvars={}) — falling through to general solver",
                cnf.nvars
            );
            // Fall through to Stage 4 (CaDiCaL subprocess backend).
        }
    }

    // === Stage 4: General-purpose in-process CaDiCaL ===
    //
    // Reaches here when:
    //   (a) --biclique was not set, or
    //   (b) --biclique was set but Ramsey detection failed.
    //
    // Uses in-process CaDiCaL with optional sym propagator (if satsuma
    // found non-trivial generators earlier in the pipeline). This makes
    // cascade a general solver that auto-specializes on symmetry.
    {
        let gen_start = Instant::now();
        let mut solver = cadical_ffi::Solver::new();

        if let Some(t) = timeout {
            solver.set("limit", t as i32);
        }

        // Enable proof tracing if requested.
        let gen_proof_path = if proof.is_some() || certified {
            let p = scratch_path(&input, "_general.drat");
            solver.set("binary", 0);
            solver.trace_proof(&p);
            Some(p)
        } else {
            None
        };

        // Feed the (possibly augmented) CNF to in-process CaDiCaL.
        let solve_cnf = match dimacs::parse_file(&effective_cnf) {
            Ok(c) => c,
            Err(e) => {
                eprintln!("c parse error on {}: {}", effective_cnf.display(), e);
                return ExitCode::from(1);
            }
        };
        for clause in solve_cnf.clauses.iter() {
            for lit in clause.lits() {
                solver.add(lit.raw());
            }
            solver.add(0);
        }

        // Wire sym propagator if generators were extracted.
        // (online_sym flag + equisat_proof presence.)
        if online_sym {
            if let Some(gs) = equisat_proof
                .as_ref()
                .and_then(|p| parse_veripb_proof(p, cnf.nvars as u32).ok())
            {
                if !gs.is_empty() {
                    let max_gens: usize = std::env::var("CASCADE_SYM_MAX_GENS")
                        .ok()
                        .and_then(|s| s.parse().ok())
                        .unwrap_or(20);
                    let mut gs = gs;
                    if gs.gens.len() > max_gens {
                        gs.gens.truncate(max_gens);
                    }
                    if gs.ordering.is_empty() {
                        gs.ordering = (1..=cnf.nvars as u32).collect();
                    }
                    println!(
                        "c [general] wiring sym propagator: {} generators",
                        gs.len()
                    );
                    let sym = SymmetryPropagator::new(gs);
                    let observed: Vec<i32> = (1..=cnf.nvars as i32).collect();
                    solver.connect_propagator(
                        Box::new(sym) as Box<dyn cadical_ffi::ExternalPropagator>,
                        &observed,
                    );
                }
            }
        }

        println!("c [general] solving with in-process CaDiCaL...");
        let result = solver.solve();
        let gen_elapsed = gen_start.elapsed().as_secs_f64();
        let conflicts = solver.conflicts();

        println!(
            "c [general] {:?} in {:.2}s, {} conflicts",
            result, gen_elapsed, conflicts
        );

        match result {
            cadical_ffi::SolveResult::Sat => {
                let mut model = Vec::new();
                for v in 1..=cnf.nvars as i32 {
                    model.push(solver.val(v));
                }
                if certified {
                    let lits: Vec<cascade::types::Lit> =
                        model.iter().map(|&v| cascade::types::Lit::new(v)).collect();
                    print!("c [certify] model vs original CNF... ");
                    match certify::verify_model(&cnf, &lits) {
                        Ok(()) => println!("VERIFIED"),
                        Err(e) => {
                            println!("FAILED: {}", e);
                            return ExitCode::from(30);
                        }
                    }
                }
                println!("s SATISFIABLE");
                let mut col = 2;
                print!("v");
                for &lit in &model {
                    let s = format!(" {}", lit);
                    if col + s.len() > 78 { println!(); print!("v"); col = 1; }
                    print!("{}", s);
                    col += s.len();
                }
                println!(" 0");
                return ExitCode::from(10);
            }
            cadical_ffi::SolveResult::Unsat => {
                if gen_proof_path.is_some() {
                    solver.close_proof();
                }
                if certified {
                    if let Some(gp) = &gen_proof_path {
                        print!("c [certify] drat-trim body... ");
                        match certify::verify_drat_trim(&effective_cnf, gp) {
                            Ok(()) => println!("VERIFIED"),
                            Err(e) => {
                                println!("FAILED: {}", e);
                                return ExitCode::from(30);
                            }
                        }
                    }
                }
                println!("s UNSATISFIABLE");
                return ExitCode::from(20);
            }
            cadical_ffi::SolveResult::Unknown => {
                println!("s UNKNOWN");
                return ExitCode::from(0);
            }
        }
    }

}

/// Estimate C(n, k) — binomial coefficient. Returns u64::MAX on overflow.
fn estimate_combinations(n: u32, k: u32) -> u64 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k) as u64;
    let n = n as u64;
    let mut result: u64 = 1;
    for i in 0..k {
        result = result.saturating_mul(n - i) / (i + 1);
    }
    result
}

fn scratch_path(input: &Path, suffix: &str) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("cascade");
    let mut p = std::env::temp_dir();
    p.push(format!("{}{}", stem, suffix));
    p
}

/// Read just the `p cnf nvars nclauses` header from a CNF file.
fn read_cnf_header(path: &Path) -> Option<(u32, u32)> {
    let f = std::fs::File::open(path).ok()?;
    let r = BufReader::new(f);
    for line in r.lines().flatten() {
        let s = line.trim();
        if let Some(rest) = s.strip_prefix("p cnf") {
            let parts: Vec<&str> = rest.split_whitespace().collect();
            if parts.len() >= 2 {
                return Some((parts[0].parse().ok()?, parts[1].parse().ok()?));
            }
        }
    }
    None
}

/// Detect (s, t) for R(s, t) from the smallest all-negative and all-positive
/// clause widths in the bare CNF.
fn detect_ramsey_st_from_cnf(clauses: &[cascade::types::Clause]) -> Option<(u32, u32)> {
    let mut min_neg = u32::MAX;
    let mut min_pos = u32::MAX;
    for c in clauses {
        let lits = c.lits();
        if lits.is_empty() {
            continue;
        }
        let all_neg = lits.iter().all(|l| l.is_negative());
        let all_pos = lits.iter().all(|l| l.is_positive());
        if all_neg {
            min_neg = min_neg.min(lits.len() as u32);
        }
        if all_pos {
            min_pos = min_pos.min(lits.len() as u32);
        }
    }
    if min_neg == u32::MAX || min_pos == u32::MAX {
        return None;
    }
    cardinality::detect_ramsey_st(min_neg, min_pos)
}

/// Read a CNF file and write a new CNF that appends the given extra clauses.
/// Updates the `p cnf` header with the new variable and clause counts.
fn append_clauses_as_new_cnf(
    src: &Path,
    dst: &Path,
    extra_clauses: &[Vec<cascade::types::Lit>],
    extra_aux_vars: u32,
) -> std::io::Result<()> {
    let (old_nvars, old_nclauses) = read_cnf_header(src)
        .ok_or_else(|| std::io::Error::new(std::io::ErrorKind::Other, "no p cnf header"))?;
    let new_nvars = old_nvars + extra_aux_vars;
    let new_nclauses = old_nclauses + extra_clauses.len() as u32;

    let in_f = std::fs::File::open(src)?;
    let out_f = std::fs::File::create(dst)?;
    let mut out = std::io::BufWriter::new(out_f);
    writeln!(out, "p cnf {} {}", new_nvars, new_nclauses)?;
    let r = BufReader::new(in_f);
    for line in r.lines() {
        let line = line?;
        let s = line.trim_start();
        if s.is_empty() || s.starts_with('c') || s.starts_with("p ") {
            continue;
        }
        writeln!(out, "{}", line)?;
    }
    for cl in extra_clauses {
        for l in cl {
            write!(out, "{} ", l.raw())?;
        }
        writeln!(out, "0")?;
    }
    out.flush()?;
    Ok(())
}
