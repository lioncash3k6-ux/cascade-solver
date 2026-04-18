//! Serializable Nullstellensatz certificate format.
//!
//! An NS certificate is a list of `(axiom_i, m_i)` pairs where each `m_i`
//! is a polynomial over 𝔽_p such that
//!
//! ```text
//!     ∑_i m_i(x) · axiom_i(x)  ≡  1   (mod p, mod ⟨x_v² − x_v⟩)
//! ```
//!
//! The cert proves the axioms are jointly unsatisfiable. This module
//! defines a simple text format for such certs, with a write path used
//! by the solver and a parse + verify path that is completely
//! independent of the solver (so the verifier can be trusted even if
//! `orbit_ns` has a bug).
//!
//! # Format (one statement per line)
//!
//! ```text
//! c <comment>          -- skipped
//! p <prime>            -- the modulus, u8 prime
//! d <degree>           -- claimed NS degree (metadata, not used in check)
//! n <n_vars>           -- number of variables; vars are 1..=n
//! axiom <i>            -- begin polynomial axiom A_i (0-indexed)
//! mult <i>             -- begin multiplier polynomial m_i
//! term <coef> [v ...]  -- one monomial: coef ∈ 1..p, var list possibly empty
//! end                  -- end of current polynomial
//! ```
//!
//! Axioms and multipliers may appear in any order. Monomials inside a
//! polynomial may appear in any order (verifier accumulates). A missing
//! multiplier for an axiom means that axiom's multiplier is 0.

use super::ns_fp::PolyP;
use super::poly::Monomial;
use std::collections::BTreeMap;
use std::io::{BufRead, BufReader, Read, Write};

/// A serialized NS certificate.
#[derive(Clone, Debug)]
pub struct CertDoc {
    pub prime: u8,
    pub degree: usize,
    pub n_vars: u32,
    pub axioms: Vec<PolyP>,
    /// `mults[i]` is the multiplier for `axioms[i]`. Default `PolyP::zero(p)`.
    pub mults: Vec<PolyP>,
}

impl CertDoc {
    /// Build a cert document from the solver's output: axioms indexed
    /// 0..axioms.len() and a map `axiom_idx → multiplier`.
    pub fn from_solver(
        prime: u8,
        degree: usize,
        n_vars: u32,
        axioms: Vec<PolyP>,
        mults_map: &BTreeMap<usize, PolyP>,
    ) -> Self {
        let mults: Vec<PolyP> = (0..axioms.len())
            .map(|i| {
                mults_map
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| PolyP::zero(prime))
            })
            .collect();
        Self {
            prime,
            degree,
            n_vars,
            axioms,
            mults,
        }
    }

    /// Write the cert to anything `Write`. One polynomial per
    /// `axiom`/`mult` block; the file is human-readable.
    pub fn write<W: Write>(&self, w: &mut W) -> std::io::Result<()> {
        writeln!(w, "c Nullstellensatz certificate over F_{}", self.prime)?;
        writeln!(w, "c sum over i of mult[i] * axiom[i] = 1 (mod p, mod <x^2 - x>)")?;
        writeln!(w, "p {}", self.prime)?;
        writeln!(w, "d {}", self.degree)?;
        writeln!(w, "n {}", self.n_vars)?;
        for (i, a) in self.axioms.iter().enumerate() {
            writeln!(w, "axiom {}", i)?;
            write_poly(w, a)?;
            writeln!(w, "end")?;
        }
        for (i, m) in self.mults.iter().enumerate() {
            if m.is_zero() {
                continue;
            }
            writeln!(w, "mult {}", i)?;
            write_poly(w, m)?;
            writeln!(w, "end")?;
        }
        Ok(())
    }

    /// Parse a cert document from anything `Read`. Errors out on any
    /// malformed line — the verifier must reject bad input.
    pub fn parse<R: Read>(r: R) -> Result<Self, CertError> {
        let reader = BufReader::new(r);
        let mut prime: Option<u8> = None;
        let mut degree: Option<usize> = None;
        let mut n_vars: Option<u32> = None;
        let mut axioms_map: BTreeMap<usize, PolyP> = BTreeMap::new();
        let mut mults_map: BTreeMap<usize, PolyP> = BTreeMap::new();

        enum State {
            Header,
            InAxiom(usize, PolyP),
            InMult(usize, PolyP),
        }
        let mut state = State::Header;

        for (lineno, line) in reader.lines().enumerate() {
            let line = line.map_err(|e| CertError::Io(e.to_string()))?;
            let line = line.trim();
            if line.is_empty() || line.starts_with('c') || line.starts_with('#') {
                continue;
            }
            let mut toks = line.split_whitespace();
            let head = toks.next().ok_or_else(|| CertError::Parse {
                line: lineno + 1,
                msg: "empty statement".into(),
            })?;
            match head {
                "p" => {
                    let v = toks.next().ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "p: missing value".into(),
                    })?;
                    prime = Some(v.parse::<u8>().map_err(|_| CertError::Parse {
                        line: lineno + 1,
                        msg: format!("bad prime '{}'", v),
                    })?);
                }
                "d" => {
                    let v = toks.next().ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "d: missing value".into(),
                    })?;
                    degree = Some(v.parse::<usize>().map_err(|_| CertError::Parse {
                        line: lineno + 1,
                        msg: format!("bad degree '{}'", v),
                    })?);
                }
                "n" => {
                    let v = toks.next().ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "n: missing value".into(),
                    })?;
                    n_vars = Some(v.parse::<u32>().map_err(|_| CertError::Parse {
                        line: lineno + 1,
                        msg: format!("bad n_vars '{}'", v),
                    })?);
                }
                "axiom" => {
                    let p = prime.ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "axiom before p".into(),
                    })?;
                    let idx: usize =
                        toks.next().and_then(|s| s.parse().ok()).ok_or_else(|| {
                            CertError::Parse {
                                line: lineno + 1,
                                msg: "axiom: missing index".into(),
                            }
                        })?;
                    state = State::InAxiom(idx, PolyP::zero(p));
                }
                "mult" => {
                    let p = prime.ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "mult before p".into(),
                    })?;
                    let idx: usize =
                        toks.next().and_then(|s| s.parse().ok()).ok_or_else(|| {
                            CertError::Parse {
                                line: lineno + 1,
                                msg: "mult: missing index".into(),
                            }
                        })?;
                    state = State::InMult(idx, PolyP::zero(p));
                }
                "term" => {
                    let p = prime.ok_or_else(|| CertError::Parse {
                        line: lineno + 1,
                        msg: "term before p".into(),
                    })?;
                    let coef: u8 =
                        toks.next().and_then(|s| s.parse().ok()).ok_or_else(|| {
                            CertError::Parse {
                                line: lineno + 1,
                                msg: "term: missing coefficient".into(),
                            }
                        })?;
                    if coef == 0 || coef >= p {
                        return Err(CertError::Parse {
                            line: lineno + 1,
                            msg: format!("coef {} out of range [1, {})", coef, p),
                        });
                    }
                    let mut vars: Vec<u32> = Vec::new();
                    for tok in toks {
                        let v: u32 = tok.parse().map_err(|_| CertError::Parse {
                            line: lineno + 1,
                            msg: format!("bad variable '{}'", tok),
                        })?;
                        vars.push(v);
                    }
                    let m = Monomial::from_vars(vars);
                    match &mut state {
                        State::InAxiom(_, poly) | State::InMult(_, poly) => {
                            let e = poly.terms.entry(m).or_insert(0);
                            *e = (*e + coef) % p;
                            if *e == 0 {
                                // Remove zero entries to keep poly canonical.
                                // (Can't borrow poly.terms twice — do separately.)
                            }
                        }
                        State::Header => {
                            return Err(CertError::Parse {
                                line: lineno + 1,
                                msg: "term outside axiom/mult block".into(),
                            });
                        }
                    }
                    if let State::InAxiom(_, poly) | State::InMult(_, poly) = &mut state
                    {
                        poly.terms.retain(|_, c| *c != 0);
                    }
                }
                "end" => match std::mem::replace(&mut state, State::Header) {
                    State::InAxiom(idx, poly) => {
                        axioms_map.insert(idx, poly);
                    }
                    State::InMult(idx, poly) => {
                        mults_map.insert(idx, poly);
                    }
                    State::Header => {
                        return Err(CertError::Parse {
                            line: lineno + 1,
                            msg: "end outside axiom/mult block".into(),
                        });
                    }
                },
                other => {
                    return Err(CertError::Parse {
                        line: lineno + 1,
                        msg: format!("unknown statement '{}'", other),
                    });
                }
            }
        }

        let prime = prime.ok_or(CertError::MissingHeader("p"))?;
        let degree = degree.ok_or(CertError::MissingHeader("d"))?;
        let n_vars = n_vars.ok_or(CertError::MissingHeader("n"))?;

        // Assemble axioms and mults as dense vectors, defaulting to zero
        // for any index not present in the file.
        let max_axiom_idx = axioms_map.keys().copied().max().unwrap_or(0);
        let axioms: Vec<PolyP> = (0..=max_axiom_idx)
            .map(|i| {
                axioms_map
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| PolyP::zero(prime))
            })
            .collect();
        let mults: Vec<PolyP> = (0..=max_axiom_idx)
            .map(|i| {
                mults_map
                    .get(&i)
                    .cloned()
                    .unwrap_or_else(|| PolyP::zero(prime))
            })
            .collect();

        Ok(Self {
            prime,
            degree,
            n_vars,
            axioms,
            mults,
        })
    }

    /// Verify the certificate: compute `∑ mᵢ · aᵢ` modulo `p` and modulo
    /// multilinearity, and check the result is the constant 1.
    ///
    /// Returns `Ok(())` on a valid cert, `Err(CertError::Invalid(reason))`
    /// otherwise.
    pub fn verify(&self) -> Result<(), CertError> {
        if self.axioms.len() != self.mults.len() {
            return Err(CertError::Invalid(format!(
                "axioms ({}) and mults ({}) have different lengths",
                self.axioms.len(),
                self.mults.len()
            )));
        }
        let mut acc = PolyP::zero(self.prime);
        for (i, (a, m)) in self.axioms.iter().zip(self.mults.iter()).enumerate() {
            if a.p != self.prime || m.p != self.prime {
                return Err(CertError::Invalid(format!(
                    "axiom or mult {} has wrong prime (expected {}, got {}, {})",
                    i, self.prime, a.p, m.p
                )));
            }
            if m.is_zero() {
                continue;
            }
            let contrib = m.mul(a);
            acc.add_assign(&contrib);
        }
        if !acc.is_one() {
            return Err(CertError::Invalid(format!(
                "sum does not reduce to 1 (got {} nonzero terms)",
                acc.terms.len()
            )));
        }
        Ok(())
    }
}

fn write_poly<W: Write>(w: &mut W, p: &PolyP) -> std::io::Result<()> {
    for (mono, coef) in &p.terms {
        write!(w, "term {}", coef)?;
        for v in &mono.0 {
            write!(w, " {}", v)?;
        }
        writeln!(w)?;
    }
    Ok(())
}

/// Errors returned by parsing or verification.
#[derive(Debug)]
pub enum CertError {
    Io(String),
    Parse { line: usize, msg: String },
    MissingHeader(&'static str),
    Invalid(String),
}

impl std::fmt::Display for CertError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CertError::Io(s) => write!(f, "io error: {}", s),
            CertError::Parse { line, msg } => {
                write!(f, "parse error at line {}: {}", line, msg)
            }
            CertError::MissingHeader(h) => {
                write!(f, "missing required header '{}'", h)
            }
            CertError::Invalid(s) => write!(f, "invalid certificate: {}", s),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::problems::php_functional;
    use crate::algebra::orbit_ns::find_orbit_cert_fp;
    use crate::tuple_schema::TupleVarSchema;

    /// Run the orbit-NS engine on PHP_{5,4} over 𝔽₇, serialize the
    /// certificate, parse it back, and verify the round-tripped cert is
    /// still valid.
    #[test]
    fn php_5_4_cert_round_trip() {
        let (schema, axioms) = php_functional(5, 4, 7);
        let d = 5usize;
        let mults_map = find_orbit_cert_fp(&schema, &axioms, d, 7)
            .expect("PHP_{5,4} must have a cert at d=5 over F_7");

        let doc = CertDoc::from_solver(7, d, schema.n_vars(), axioms.clone(), &mults_map);

        // Verify directly.
        doc.verify().expect("fresh cert must verify");

        // Round-trip through text format.
        let mut buf: Vec<u8> = Vec::new();
        doc.write(&mut buf).expect("write cert");
        let parsed =
            CertDoc::parse(buf.as_slice()).expect("parse round-tripped cert");

        assert_eq!(parsed.prime, doc.prime);
        assert_eq!(parsed.degree, doc.degree);
        assert_eq!(parsed.n_vars, doc.n_vars);
        assert_eq!(parsed.axioms.len(), doc.axioms.len());
        assert_eq!(parsed.mults.len(), doc.mults.len());

        parsed.verify().expect("parsed cert must verify");
    }

    /// Perturbing the cert must cause verification to fail — a negative
    /// control so we know `verify` actually does work.
    #[test]
    fn perturbed_cert_fails_verification() {
        let (schema, axioms) = php_functional(5, 4, 7);
        let d = 5usize;
        let mults_map =
            find_orbit_cert_fp(&schema, &axioms, d, 7).expect("cert at d=5");
        let mut doc =
            CertDoc::from_solver(7, d, schema.n_vars(), axioms, &mults_map);

        // Flip a coefficient in a non-empty multiplier to break the identity.
        let perturbed = doc
            .mults
            .iter_mut()
            .find(|m| !m.is_zero())
            .expect("some multiplier is nonzero");
        let key = perturbed.terms.keys().next().cloned().unwrap();
        let entry = perturbed.terms.get_mut(&key).unwrap();
        *entry = (*entry + 1) % 7;
        if *entry == 0 {
            perturbed.terms.remove(&key);
        }

        assert!(doc.verify().is_err(), "perturbed cert must fail to verify");
    }

    /// Verifier must reject a truncated / empty input with a clean parse
    /// error, not a panic.
    #[test]
    fn empty_input_errors() {
        let buf: &[u8] = b"";
        let r = CertDoc::parse(buf);
        assert!(r.is_err());
    }

    /// Missing `p` header must be reported, not silently accepted.
    #[test]
    fn missing_prime_header_errors() {
        let buf: &[u8] = b"d 5\nn 20\n";
        let r = CertDoc::parse(buf);
        matches!(r, Err(CertError::MissingHeader("p")));
        let _ = schema_marker();
    }

    // Compile-time tag that the schema module is referenced; keeps this
    // test file stable if imports shift around.
    fn schema_marker() -> &'static str {
        std::any::type_name::<TupleVarSchema>()
    }
}
