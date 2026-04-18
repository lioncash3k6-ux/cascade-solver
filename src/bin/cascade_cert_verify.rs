//! Standalone NS-certificate verifier.
//!
//! Reads a certificate file written by `cascade --alg-cert <path>` and
//! independently checks that
//!
//! ```text
//!     ∑_i mult[i] · axiom[i]  ≡  1   (mod p, mod ⟨x_v² − x_v⟩).
//! ```
//!
//! No shared state with the solver that produced the cert — the verifier
//! only trusts the cert file and the math.
//!
//! Usage:
//!
//! ```text
//!     cascade_cert_verify <cert-file>
//! ```
//!
//! Exit codes:
//!   0  — cert verified
//!   1  — cert rejected (parse error or identity does not hold)
//!   2  — usage error

use cascade::algebra::ns_cert::{CertDoc, CertError};
use std::env;
use std::fs::File;
use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} <cert-file>", args[0]);
        return ExitCode::from(2);
    }
    let path = &args[1];

    let f = match File::open(path) {
        Ok(f) => f,
        Err(e) => {
            eprintln!("cannot open '{}': {}", path, e);
            return ExitCode::from(1);
        }
    };

    let doc = match CertDoc::parse(f) {
        Ok(d) => d,
        Err(e) => {
            eprintln!("parse error: {}", e);
            return ExitCode::from(1);
        }
    };

    println!(
        "c loaded: prime={} degree={} n_vars={} axioms={} nonzero_mults={}",
        doc.prime,
        doc.degree,
        doc.n_vars,
        doc.axioms.len(),
        doc.mults.iter().filter(|m| !m.is_zero()).count()
    );

    match doc.verify() {
        Ok(()) => {
            println!("s VERIFIED");
            ExitCode::from(0)
        }
        Err(CertError::Invalid(msg)) => {
            println!("s REJECTED  {}", msg);
            ExitCode::from(1)
        }
        Err(e) => {
            println!("s REJECTED  {}", e);
            ExitCode::from(1)
        }
    }
}
