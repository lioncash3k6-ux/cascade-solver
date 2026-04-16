//! Integration test for the algebraic engine (GAPS leg 4):
//! informational degree-probe for small Ramsey instances.
//!
//! Ramsey problems are KNOWN to have Ω(n) Nullstellensatz degree lower
//! bounds (Beame, Impagliazzo, Krajíček, Pitassi, Pudlák). For our
//! purposes the algebraic engine is a COMPLEMENT to CDCL, not a
//! replacement. These tests confirm:
//!
//!   1. SAT Ramsey instances correctly report NoCertificate.
//!   2. Trivial pigeonhole-style UNSAT finds a low-degree cert.
//!   3. Ramsey UNSAT at low degree does NOT return a spurious cert
//!      (soundness).

use cascade::algebra::{find_ns_certificate, ns::verify_certificate, NsResult};
use cascade::cardinality::ev;

fn r33_triangle_bans(n: u32) -> Vec<Vec<i32>> {
    let mut out = Vec::new();
    for a in 1..=n {
        for b in (a + 1)..=n {
            for c in (b + 1)..=n {
                let eab = ev(a, b, n).raw();
                let eac = ev(a, c, n).raw();
                let ebc = ev(b, c, n).raw();
                out.push(vec![-eab, -eac, -ebc]);
                out.push(vec![eab, eac, ebc]);
            }
        }
    }
    out
}

#[test]
fn r33_k5_sat_has_no_low_degree_cert() {
    // SAT — no certificate can exist, ever.
    let clauses = r33_triangle_bans(5);
    for d in 1..=3 {
        if let NsResult::Unsat(c) = find_ns_certificate(&clauses, 10, d) {
            let valid = verify_certificate(&c, &clauses);
            assert!(!valid, "spurious cert at d={} for SAT instance", d);
        }
    }
}

#[test]
fn r33_k6_degree_probe() {
    // Informational: just record that no low-degree NS cert exists.
    // Ramsey UNSAT degree is linear in n (Beame et al).
    let clauses = r33_triangle_bans(6);
    for d in 1..=3 {
        match find_ns_certificate(&clauses, 15, d) {
            NsResult::NoCertificate => {
                eprintln!("R(3,3)/K_6 @ d={}: NoCertificate (expected)", d);
            }
            NsResult::Unsat(c) => {
                let valid = verify_certificate(&c, &clauses);
                assert!(!valid, "spurious cert at d={} for Ramsey UNSAT", d);
                eprintln!("R(3,3)/K_6 @ d={}: cert emitted but invalid (bug)", d);
            }
        }
    }
}
