//! Demonstration: GAPS leg 4 (algebraic engine) complements leg 1
//! (CDCL) on pigeonhole instances PHP_{n+1,n}.
//!
//! Pigeonhole is the classical hard-for-resolution easy-for-polynomial-
//! calculus benchmark. The Nullstellensatz degree for PHP_{n+1,n} is
//! exactly `n` (Buss-Grigoriev-Razborov). Our naive NS-lite should
//! refute PHP_{n+1,n} at degree `n`, for small `n`, in polynomial
//! time — while CDCL alone takes exponential time.
//!
//! For small `n` (≤ 3), the test is purely a correctness check.
//! For `n = 4`+, the test doubles as a complementarity demo.

use cascade::algebra::{find_ns_certificate, ns::verify_certificate, NsResult};

/// Generate PHP_{n_pigeons, n_holes} CNF.
/// Variables: var(p, h) = (p-1)*n_holes + h for p ∈ 1..=n_pigeons, h ∈ 1..=n_holes.
fn php(n_pigeons: u32, n_holes: u32) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    let var = |p: u32, h: u32| -> i32 {
        ((p - 1) * n_holes + h) as i32
    };
    // Each pigeon goes in some hole.
    for p in 1..=n_pigeons {
        let mut clause = Vec::new();
        for h in 1..=n_holes {
            clause.push(var(p, h));
        }
        out.push(clause);
    }
    // At most one pigeon per hole.
    for h in 1..=n_holes {
        for p1 in 1..=n_pigeons {
            for p2 in (p1 + 1)..=n_pigeons {
                out.push(vec![-var(p1, h), -var(p2, h)]);
            }
        }
    }
    out
}

#[test]
fn php_2_1_ns_degree_2() {
    // 2 pigeons in 1 hole. Vars: x1 (p1 in h1), x2 (p2 in h1).
    // Clauses: x1, x2, ¬x1 ∨ ¬x2.
    let clauses: Vec<Vec<i32>> = vec![vec![1], vec![2], vec![-1, -2]];
    match find_ns_certificate(&clauses, 2, 2) {
        NsResult::Unsat(cert) => {
            assert!(verify_certificate(&cert, &clauses), "verify failed");
            eprintln!(
                "PHP_{{2,1}} at d=2: {} cert terms",
                cert.terms.len()
            );
            for t in &cert.terms {
                eprintln!("  clause {} · {:?}", t.clause_idx, t.multiplier);
            }
        }
        NsResult::NoCertificate => {
            panic!("PHP_2_1 must have degree-2 cert");
        }
    }
}

#[test]
fn php_3_2_ns_degree_probe() {
    // 3 pigeons, 2 holes. 6 vars, 9 clauses. UNSAT.
    // The exact NS degree over 𝔽₂ is a research question; probe
    // 2..=5 and report where a cert first appears.
    let clauses = php(3, 2);
    assert_eq!(clauses.len(), 9);

    let mut found_at: Option<usize> = None;
    for d in 2..=5 {
        match find_ns_certificate(&clauses, 6, d) {
            NsResult::Unsat(cert) => {
                if verify_certificate(&cert, &clauses) {
                    eprintln!(
                        "PHP_{{3,2}} at d={}: valid cert, {} terms",
                        d,
                        cert.terms.len()
                    );
                    found_at = Some(d);
                    break;
                } else {
                    eprintln!("PHP_{{3,2}} at d={}: cert returned but verify FAILED", d);
                }
            }
            NsResult::NoCertificate => {
                eprintln!("PHP_{{3,2}} at d={}: no cert", d);
            }
        }
    }
    assert!(
        found_at.is_some(),
        "PHP_3_2 is UNSAT; must have some low-degree NS cert"
    );
}

#[test]
#[ignore]
fn php_4_3_ns_degree_probe() {
    // 4 pigeons, 3 holes. 12 vars, 22 clauses. UNSAT.
    let clauses = php(4, 3);
    assert_eq!(clauses.len(), 22);

    let mut found_at: Option<(usize, f64, usize)> = None;
    for d in 3..=6 {
        let t = std::time::Instant::now();
        match find_ns_certificate(&clauses, 12, d) {
            NsResult::Unsat(cert) => {
                let elapsed = t.elapsed().as_secs_f64();
                if verify_certificate(&cert, &clauses) {
                    eprintln!(
                        "PHP_{{4,3}} at d={}: valid cert, {} terms, {:.2}s",
                        d,
                        cert.terms.len(),
                        elapsed
                    );
                    found_at = Some((d, elapsed, cert.terms.len()));
                    break;
                }
            }
            NsResult::NoCertificate => {
                eprintln!("PHP_{{4,3}} at d={}: no cert ({:.2}s)", d, t.elapsed().as_secs_f64());
            }
        }
    }
    assert!(
        found_at.is_some(),
        "PHP_4_3 is UNSAT; must have some low-degree NS cert (tried up to d=6)"
    );
}

#[test]
#[ignore] // expensive at degree 5; opt in with `cargo test -- --ignored`
fn php_5_4_ns_degree_5() {
    // 5 pigeons, 4 holes. 20 vars, 45 clauses. UNSAT, NS degree = 5.
    let clauses = php(5, 4);
    assert_eq!(clauses.len(), 45);

    let t = std::time::Instant::now();
    match find_ns_certificate(&clauses, 20, 5) {
        NsResult::Unsat(cert) => {
            assert!(verify_certificate(&cert, &clauses));
            eprintln!(
                "PHP_{{5,4}} at d=5: valid cert, {} terms, {:.2}s",
                cert.terms.len(),
                t.elapsed().as_secs_f64()
            );
        }
        NsResult::NoCertificate => {
            panic!("expected degree-5 cert for PHP_5_4");
        }
    }
}
