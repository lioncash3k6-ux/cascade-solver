//! VeriPB (pseudo-Boolean proof) lowering for NS certificates with
//! linear axioms.
//!
//! Scope: this is the first-pass skeleton. It handles certs whose axioms
//! are *linear* polynomials (each monomial has degree ≤ 1) with integer
//! coefficients representable as `±1` — i.e. the `Count_q` family and
//! any similar family expressible as `∑ x_i = k` over 𝔽_p.
//!
//! Out of scope for this pass:
//!
//! * Non-linear axioms (PHP AMO: `x_i · x_j = 0`). Those need higher-
//!   degree PB reasoning or expansion into clausal form; work for a
//!   follow-up.
//! * Tseitin (which is genuinely modular-2 rather than integer-linear).
//!   VeriPB does not natively handle XOR; an extension path would go
//!   through the `subproof` / `redundancy` machinery.
//! * Multipliers that are not constants. For Count_q at `p = q`, the
//!   theoretical proof uses all-ones multipliers, which this module
//!   handles. Polynomial multipliers are feasible but require expanding
//!   products, which blows up cert size.
//!
//! # What this produces
//!
//! Two files: `<stem>.opb` (the input formula in PB form) and
//! `<stem>.pbp` (the derivation). External verification:
//!
//! ```text
//! veripb <stem>.opb <stem>.pbp
//! ```
//!
//! Success shows `s VERIFIED UNSAT` and exit code 0.

use super::ns_cert::CertDoc;
use super::ns_fp::PolyP;
use super::poly::Monomial;
use std::io::{self, Write};

/// A linear term in integer coefficients: `coef * x_var`. `var == 0` encodes
/// the constant term.
#[derive(Clone, Debug, PartialEq, Eq)]
struct LinTerm {
    coef: i32,
    var: u32,
}

/// Linear integer polynomial `∑ coef_i * x_i + constant`. `vars` holds
/// only the nonzero variable terms.
#[derive(Clone, Debug)]
struct LinPoly {
    vars: Vec<LinTerm>,
    constant: i32,
}

impl LinPoly {
    fn from_polyp(q: &PolyP) -> Result<Self, String> {
        let p = q.p as i32;
        let mut vars: Vec<LinTerm> = Vec::new();
        let mut constant: i32 = 0;
        for (m, &c) in &q.terms {
            // Canonical integer representative in [-p/2, p/2] so the PB
            // lowering doesn't emit needlessly large coefficients. For p
            // odd, signed form; for p=2 we keep the 0/1 form.
            let c_signed: i32 = {
                let c = c as i32;
                if p >= 3 && c > p / 2 { c - p } else { c }
            };
            if c_signed == 0 {
                continue;
            }
            match m.0.len() {
                0 => constant += c_signed,
                1 => {
                    let v = *m.0.iter().next().unwrap();
                    vars.push(LinTerm { coef: c_signed, var: v });
                }
                _ => {
                    return Err(format!(
                        "LinPoly::from_polyp: nonlinear monomial of degree {} \
                         (support {:?}); VeriPB lowering requires linear axioms",
                        m.0.len(),
                        m.0
                    ));
                }
            }
        }
        Ok(LinPoly { vars, constant })
    }

    fn is_empty(&self) -> bool {
        self.vars.is_empty() && self.constant == 0
    }

    /// True if the polynomial is a nonzero integer constant — i.e. the
    /// multiplier is a plain scalar.
    fn is_scalar(&self) -> Option<i32> {
        if self.vars.is_empty() {
            Some(self.constant)
        } else {
            None
        }
    }
}

/// Emit an OPB formula and a VeriPB proof from `cert`, under the
/// preconditions documented at the top of this module. Writes `.opb`
/// and `.pbp` at the paths given.
///
/// Returns `Ok(())` on success. If the cert violates the linear-axiom /
/// scalar-multiplier preconditions, returns an `Err` explaining which
/// invariant was violated.
pub fn emit_veripb(
    cert: &CertDoc,
    opb_out: &mut dyn Write,
    pbp_out: &mut dyn Write,
) -> Result<(), String> {
    // ---- Step 1: lift every axiom to a linear integer polynomial ----

    let linear_axioms: Vec<LinPoly> = cert
        .axioms
        .iter()
        .map(LinPoly::from_polyp)
        .collect::<Result<Vec<_>, _>>()?;

    // ---- Step 2: encode each axiom `L(x) = 0` as a PAIR of PB ----
    //
    // For `∑ a_i x_i + c = 0`, the two-sided encoding is
    //     (A) `∑ a_i x_i ≥ -c`
    //     (B) `∑ (-a_i) x_i ≥ c`
    // VeriPB numbers constraints 1..=N in the order they appear.

    writeln_io(
        opb_out,
        &format!("* #variable= {} #constraint= {}",
                 cert.n_vars, 2 * linear_axioms.len()),
    )?;

    let mut opb_constraint_ids: Vec<(u32, u32)> = Vec::new(); // (ge_id, le_id) per axiom
    let mut next_id: u32 = 1;
    for lp in &linear_axioms {
        let ge = encode_ge(lp);
        let le = encode_ge(&negate(lp));
        writeln_io(opb_out, &format!("{} ;", ge))?;
        writeln_io(opb_out, &format!("{} ;", le))?;
        opb_constraint_ids.push((next_id, next_id + 1));
        next_id += 2;
    }

    // ---- Step 3: emit the proof ----
    //
    // Strategy, for Count_q-style instances:
    //   * Sum all GE constraints with multiplier 1 → a combined GE.
    //   * Sum all LE constraints with multiplier 1 → a combined LE.
    //   * Apply `d /` to round up/down to integer bounds on `∑ x_S`.
    //   * The rounded bounds contradict.
    //
    // We keep this general: for each axiom use the scalar multiplier
    // from the cert. If the cert multiplier for axiom i is the scalar
    // c_i, we pol-accumulate `c_i` copies of the GE and LE, producing
    // `∑ c_i · (LHS_ge(A_i))` vs the negative. The resulting integer
    // identity must be contradictory if the NS cert was valid.

    writeln_io(pbp_out, "pseudo-Boolean proof version 2.0")?;
    writeln_io(pbp_out, &format!("f {}", 2 * linear_axioms.len()))?;

    // For each axiom i: multiplier m_i as a scalar integer. Only handle
    // scalars here; polynomial multipliers would require expanding
    // products and are out of scope for this skeleton.
    let mults: Vec<i32> = cert
        .mults
        .iter()
        .map(|m| {
            let lp = LinPoly::from_polyp(m).map_err(|e| {
                format!("multiplier not linear: {}", e)
            })?;
            lp.is_scalar().ok_or_else(|| {
                "multiplier has a variable term; only scalar multipliers \
                 are lowered in this skeleton".to_string()
            })
        })
        .collect::<Result<Vec<_>, String>>()?;

    // Proof strategy: sum-and-divide. If every axiom is `∑ x_i = k`
    // (with unit coefficients) and every variable appears in the same
    // number `q` of axioms, then summing gives `q · ∑_v x_v ≥ n · k`
    // and `q · ∑_v x_v ≤ n · k`. Dividing both by q (VeriPB's rule `/`
    // rounds RHS *up* in the ≥-direction), when `q ∤ n · k`, yields
    //     `∑ x_v ≥ ⌈n·k/q⌉`   and   `-∑ x_v ≥ -⌊n·k/q⌋`,
    // and adding produces `0 ≥ 1` (since ceil − floor = 1 when q ∤ n·k).
    //
    // This path works for Count_q (UNSAT iff q ∤ n) and for Tseitin on
    // a regular graph with uniform charge (UNSAT iff 2 ∤ n·c). It is
    // more general than the cert itself — the NS cert is only used as
    // an "unsat witness" that tells us to *try* this proof structure.
    let q = axiom_variable_multiplicity(&linear_axioms)
        .ok_or_else(|| {
            "VeriPB lowering requires every variable to appear in the \
             same number of axioms (Count_q / regular-graph Tseitin). \
             Non-uniform axiom systems not supported in this skeleton."
                .to_string()
        })?;
    if q == 0 {
        return Err("axiom system has no variables; nothing to prove".into());
    }
    let total_rhs: i64 = linear_axioms.iter().map(|a| (-a.constant) as i64).sum();
    if total_rhs % (q as i64) == 0 {
        return Err(format!(
            "sum-and-divide proof doesn't close: q={} divides total_rhs={}; \
             the instance may be SAT, or a different proof structure is needed",
            q, total_rhs
        ));
    }
    let _ = mults; // mults are consistency evidence; this path doesn't thread them.

    let ge_ids: Vec<u32> = opb_constraint_ids.iter().map(|p| p.0).collect();
    let le_ids: Vec<u32> = opb_constraint_ids.iter().map(|p| p.1).collect();
    let all_ones: Vec<i32> = vec![1; ge_ids.len()];

    // (1) Sum GE: `q · ∑ x >= total_rhs`.
    let ge_sum_id = emit_pol_sum(pbp_out, &ge_ids, &all_ones, next_id)?;
    next_id = ge_sum_id + 1;
    // (2) Sum LE: `-q · ∑ x >= -total_rhs`.
    let le_sum_id = emit_pol_sum(pbp_out, &le_ids, &all_ones, next_id)?;
    next_id = le_sum_id + 1;
    // (3) Divide (1) by q: `∑ x >= ⌈total_rhs / q⌉`.
    writeln_io(pbp_out, &format!("pol {} {} d", ge_sum_id, q))?;
    let ge_div_id = next_id;
    next_id += 1;
    // (4) Divide (2) by q: `-∑ x >= ⌈-total_rhs / q⌉ = -⌊total_rhs / q⌋`.
    writeln_io(pbp_out, &format!("pol {} {} d", le_sum_id, q))?;
    let le_div_id = next_id;
    next_id += 1;
    // (5) Add (3) + (4): `0 >= ⌈total_rhs/q⌉ - ⌊total_rhs/q⌋ = 1`.
    writeln_io(pbp_out, &format!("pol {} {} +", ge_div_id, le_div_id))?;
    let contradiction_id = next_id;
    let _ = next_id;

    writeln_io(pbp_out, "output NONE")?;
    writeln_io(pbp_out, &format!("conclusion UNSAT : {}", contradiction_id))?;
    writeln_io(pbp_out, "end pseudo-Boolean proof")?;

    Ok(())
}

/// If every variable in `axioms` appears in the same number `q` of
/// axioms with coefficient `+1`, return `Some(q)`. Otherwise `None`.
/// This is the precondition for the sum-and-divide proof in
/// [`emit_veripb`].
fn axiom_variable_multiplicity(axioms: &[LinPoly]) -> Option<u32> {
    let mut count_by_var: std::collections::BTreeMap<u32, u32> = Default::default();
    for ax in axioms {
        for t in &ax.vars {
            if t.coef != 1 {
                return None;
            }
            *count_by_var.entry(t.var).or_insert(0) += 1;
        }
    }
    let mut iter = count_by_var.values();
    let first = *iter.next()?;
    for &c in iter {
        if c != first {
            return None;
        }
    }
    Some(first)
}

fn writeln_io(w: &mut dyn Write, s: &str) -> Result<(), String> {
    writeln!(w, "{}", s).map_err(|e| e.to_string())
}

/// Render a PB `≥` constraint from a LinPoly `L` representing `L ≥ -L.constant`.
///
/// PB / OPB format: `+a x1 -b x2 +c x3 ... >= rhs` (RHS on right, no `;`).
fn encode_ge(lp: &LinPoly) -> String {
    let mut parts: Vec<String> = Vec::new();
    for t in &lp.vars {
        let sign = if t.coef >= 0 { "+" } else { "" };
        parts.push(format!("{}{} x{}", sign, t.coef, t.var));
    }
    let rhs = -lp.constant;
    if parts.is_empty() {
        // Empty LHS: constraint is `0 >= rhs`, which is trivial/infeasible.
        format!("0 x1 >= {}", rhs) // degenerate; LHS reads as "zero constraint"
    } else {
        format!("{} >= {}", parts.join(" "), rhs)
    }
}

fn negate(lp: &LinPoly) -> LinPoly {
    LinPoly {
        vars: lp
            .vars
            .iter()
            .map(|t| LinTerm {
                coef: -t.coef,
                var: t.var,
            })
            .collect(),
        constant: -lp.constant,
    }
}

/// Emit a VeriPB `pol` instruction that computes `∑ mults[i] * ids[i]`
/// (integer linear combination) and assigns the result the next
/// available id. Returns that id.
///
/// Reverse-Polish form: `pol ID_0 MULT_0 * ID_1 MULT_1 * + ID_2 MULT_2 * + ...`
/// for `ID_0 * MULT_0 + ID_1 * MULT_1 + ...`. Zero multipliers are skipped.
fn emit_pol_sum(
    out: &mut dyn Write,
    ids: &[u32],
    mults: &[i32],
    next_id: u32,
) -> Result<u32, String> {
    assert_eq!(ids.len(), mults.len());
    let pairs: Vec<(u32, i32)> = ids
        .iter()
        .zip(mults.iter())
        .filter_map(|(&id, &m)| if m != 0 { Some((id, m)) } else { None })
        .collect();
    if pairs.is_empty() {
        return Err("emit_pol_sum: all multipliers zero".to_string());
    }
    let mut expr = String::new();
    for (i, &(id, m)) in pairs.iter().enumerate() {
        if m == 1 {
            expr.push_str(&format!("{} ", id));
        } else {
            expr.push_str(&format!("{} {} * ", id, m));
        }
        if i >= 1 {
            expr.push_str("+ ");
        }
    }
    writeln_io(out, &format!("pol {}", expr.trim()))?;
    Ok(next_id)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::problems::count_q_partition;

    #[test]
    fn count_q_n4_q3_emits_veripb_for_linear_axioms() {
        // Count_3 on [4]: UNSAT over 𝔽_3 at d=1. All multipliers should
        // be the scalar 1; axioms are linear. Both preconditions satisfied.
        let (schema, axioms) = count_q_partition(4, 3, 3);
        let n_vars = schema.n_vars();

        // Build a "toy cert" by hand: multiplier = 1 for every axiom.
        // (The real orbit engine produces the same thing at d=1 over 𝔽_3.)
        let mults: Vec<PolyP> = (0..axioms.len())
            .map(|_| {
                let mut terms = std::collections::BTreeMap::new();
                terms.insert(Monomial::one(), 1u8);
                PolyP { p: 3, terms }
            })
            .collect();
        let cert = CertDoc {
            prime: 3,
            degree: 1,
            n_vars,
            axioms,
            mults,
        };

        let mut opb: Vec<u8> = Vec::new();
        let mut pbp: Vec<u8> = Vec::new();
        emit_veripb(&cert, &mut opb, &mut pbp).expect("lowering should succeed");

        let opb_str = String::from_utf8(opb).unwrap();
        let pbp_str = String::from_utf8(pbp).unwrap();

        // Sanity: OPB has one line per-constraint declaration plus header.
        assert!(opb_str.starts_with("* #variable= 4 #constraint= 8\n"));
        // 4 vertex axioms × 2 directions = 8 constraints.
        assert_eq!(opb_str.lines().filter(|l| l.ends_with(';')).count(), 8);

        // PBP has the proof-version header + contradiction.
        assert!(pbp_str.starts_with("pseudo-Boolean proof version 2.0\n"));
        assert!(pbp_str.contains("pol "));
        assert!(pbp_str.contains("conclusion UNSAT"));
    }
}
