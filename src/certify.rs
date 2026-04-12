//! Certified verification: external tool invocation for proof checking.
//!
//! Under `--certified` mode, every verdict is independently verified:
//!   - UNSAT: veripb confirms equisat, drat-trim confirms body proof
//!   - SAT: model checked clause-by-clause against the ORIGINAL CNF

use crate::dimacs::Cnf;
use crate::types::Lit;
use std::path::Path;
use std::process::Command;

#[derive(Debug)]
pub enum CertifyError {
    VeripbFailed(String),
    DratTrimFailed(String),
    ModelInvalid { violated: usize, total: usize },
    ToolNotFound(String),
    IoError(String),
}

impl std::fmt::Display for CertifyError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertifyError::VeripbFailed(s) => write!(f, "veripb verification failed: {}", s),
            CertifyError::DratTrimFailed(s) => write!(f, "drat-trim verification failed: {}", s),
            CertifyError::ModelInvalid { violated, total } => {
                write!(f, "model invalid: {}/{} clauses violated", violated, total)
            }
            CertifyError::ToolNotFound(s) => write!(f, "verification tool not found: {}", s),
            CertifyError::IoError(s) => write!(f, "I/O error: {}", s),
        }
    }
}

pub fn verify_veripb(bare_cnf: &Path, proof: &Path) -> Result<(), CertifyError> {
    let output = Command::new("veripb")
        .arg(bare_cnf)
        .arg(proof)
        .output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                CertifyError::ToolNotFound("veripb".into())
            } else {
                CertifyError::IoError(e.to_string())
            }
        })?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{}{}", stdout, stderr);

    if combined.contains("s VERIFIED") {
        Ok(())
    } else {
        Err(CertifyError::VeripbFailed(
            combined.lines().last().unwrap_or("unknown error").to_string(),
        ))
    }
}

pub fn verify_drat_trim(cnf: &Path, proof: &Path) -> Result<(), CertifyError> {
    let output = Command::new("drat-trim")
        .arg(cnf)
        .arg(proof)
        .output()
        .map_err(|e| {
            if e.kind() == std::io::ErrorKind::NotFound {
                CertifyError::ToolNotFound("drat-trim".into())
            } else {
                CertifyError::IoError(e.to_string())
            }
        })?;

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let combined = format!("{}{}", stdout, stderr);

    if combined.contains("s VERIFIED") {
        Ok(())
    } else {
        Err(CertifyError::DratTrimFailed(
            combined.lines().last().unwrap_or("unknown error").to_string(),
        ))
    }
}

pub fn verify_model(original_cnf: &Cnf, model: &[Lit]) -> Result<(), CertifyError> {
    let mut assign = vec![0i8; original_cnf.nvars as usize + 1];
    for &lit in model {
        let v = lit.var().0 as usize;
        if v > 0 && v <= original_cnf.nvars as usize {
            assign[v] = if lit.is_positive() { 1 } else { -1 };
        }
    }

    let total = original_cnf.clauses.len();
    let mut violated = 0usize;

    for clause in &original_cnf.clauses {
        let satisfied = clause.lits().iter().any(|&lit| {
            let v = lit.var().0 as usize;
            if v == 0 || v > original_cnf.nvars as usize {
                return false;
            }
            let val = if lit.is_positive() { 1i8 } else { -1i8 };
            assign[v] == val
        });
        if !satisfied {
            violated += 1;
        }
    }

    if violated == 0 {
        Ok(())
    } else {
        Err(CertifyError::ModelInvalid { violated, total })
    }
}

/// Write cardinality clauses as DRAT additions to a file.
pub fn write_card_drat_proof(
    proof_path: &Path,
    clauses: &[Vec<Lit>],
) -> Result<(), CertifyError> {
    use std::io::Write;
    let f = std::fs::File::create(proof_path)
        .map_err(|e| CertifyError::IoError(e.to_string()))?;
    let mut out = std::io::BufWriter::new(f);
    for cl in clauses {
        for l in cl {
            write!(out, "{} ", l.raw())
                .map_err(|e| CertifyError::IoError(e.to_string()))?;
        }
        writeln!(out, "0").map_err(|e| CertifyError::IoError(e.to_string()))?;
    }
    out.flush().map_err(|e| CertifyError::IoError(e.to_string()))?;
    Ok(())
}

/// Prepend cardinality DRAT additions to a body proof, creating a combined
/// proof that drat-trim can verify end-to-end against the pre-cardinality CNF.
pub fn combine_card_and_body_proof(
    card_clauses: &[Vec<Lit>],
    body_proof: &Path,
    combined_proof: &Path,
) -> Result<(), CertifyError> {
    use std::io::{Read, Write};
    let f = std::fs::File::create(combined_proof)
        .map_err(|e| CertifyError::IoError(e.to_string()))?;
    let mut out = std::io::BufWriter::new(f);
    // Write cardinality additions first
    for cl in card_clauses {
        for l in cl {
            write!(out, "{} ", l.raw())
                .map_err(|e| CertifyError::IoError(e.to_string()))?;
        }
        writeln!(out, "0").map_err(|e| CertifyError::IoError(e.to_string()))?;
    }
    // Append body proof
    let mut body = std::fs::File::open(body_proof)
        .map_err(|e| CertifyError::IoError(e.to_string()))?;
    let mut buf = Vec::new();
    body.read_to_end(&mut buf)
        .map_err(|e| CertifyError::IoError(e.to_string()))?;
    out.write_all(&buf)
        .map_err(|e| CertifyError::IoError(e.to_string()))?;
    out.flush().map_err(|e| CertifyError::IoError(e.to_string()))?;
    Ok(())
}
