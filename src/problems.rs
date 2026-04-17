//! Problem-family factories.
//!
//! Each factory returns `(TupleVarSchema, Vec<PolyP>)`: the variable-tuple
//! schema describing how variables correspond to structured tuples, and a
//! list of polynomial axioms over 𝔽_p encoding the problem. The orbit-reduced
//! NS engine in [`crate::algebra::orbit_ns`] is problem-agnostic; all
//! problem-specific logic lives here.

use crate::algebra::ns_fp::PolyP;
use crate::algebra::poly::Monomial;
use crate::tuple_schema::{BaseSet, GroupSpec, TupleKind, TupleVarSchema};
use std::collections::BTreeMap;

/// Functional pigeonhole principle PHP_{P,H}.
///
/// * Schema: ordered pairs `(p, h)` with `p ∈ 1..=P`, `h ∈ 1..=H`.
/// * Group: full product `S_P × S_H`.
/// * Axioms:
///   - `P` pigeon-totality equations `∑_h x(p,h) − 1 = 0` (degree 1).
///   - `H · C(P, 2)` AMO equations `x(p1, h) · x(p2, h) = 0` (degree 2).
pub fn php_functional(
    n_pigeons: u32,
    n_holes: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    let schema = TupleVarSchema {
        bases: vec![
            BaseSet::new("P", n_pigeons),
            BaseSet::new("H", n_holes),
        ],
        tuple_kind: TupleKind::Ordered,
        group: GroupSpec::FullProduct,
    };

    let mut axioms: Vec<PolyP> = Vec::new();

    // Pigeon totality.
    for p in 1..=n_pigeons {
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        for h in 1..=n_holes {
            let v = schema.var_of_tuple(&[p, h]);
            terms.insert(Monomial::single(v), 1);
        }
        terms.insert(Monomial::one(), prime - 1); // -1 mod p
        axioms.push(PolyP {
            p: prime,
            terms,
        });
    }
    // AMO per hole.
    for h in 1..=n_holes {
        for p1 in 1..=n_pigeons {
            for p2 in (p1 + 1)..=n_pigeons {
                let va = schema.var_of_tuple(&[p1, h]);
                let vb = schema.var_of_tuple(&[p2, h]);
                let mut terms = BTreeMap::new();
                terms.insert(Monomial::from_vars([va, vb]), 1u8);
                axioms.push(PolyP {
                    p: prime,
                    terms,
                });
            }
        }
    }
    (schema, axioms)
}

/// Ramsey R(s, t) on K_n: CNF-style disjunctive encoding, for infrastructure
/// demo only (NS degree Ω(n) makes this intractable at interesting sizes).
///
/// * Schema: unordered vertex pairs.
/// * Group: `S_n` acting on vertices (diagonal on pair coordinates).
/// * Axioms: red clique ban (no `s` vertices all red) + blue clique ban.
pub fn ramsey_disjunctive(
    s: u32,
    t: u32,
    n: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedPair,
        group: GroupSpec::Diagonal,
    };

    let mut axioms: Vec<PolyP> = Vec::new();

    // Red K_s ban: for each S ⊆ [n] with |S| = s, the polynomial
    // ∏_{{a,b} ⊆ S} x({a,b})  = 1 iff all edges in S are red (violation).
    // As an axiom this polynomial must vanish on models, so it IS the clause.
    for combo in combinations(n, s as usize) {
        let mut vars = Vec::new();
        for i in 0..combo.len() {
            for j in (i + 1)..combo.len() {
                vars.push(schema.var_of_tuple(&[combo[i], combo[j]]));
            }
        }
        // Axiom: ∏ x(edge) — vanishes unless every edge in S is red.
        let mut terms = BTreeMap::new();
        terms.insert(Monomial::from_vars(vars), 1u8);
        axioms.push(PolyP {
            p: prime,
            terms,
        });
    }

    // Blue K_t ban: ∏ (1 − x(edge)) = 1 iff all t(t-1)/2 edges are blue
    // (i.e., x = 0 for each). Expand as multilinear polynomial.
    for combo in combinations(n, t as usize) {
        let mut factors: Vec<PolyP> = Vec::new();
        for i in 0..combo.len() {
            for j in (i + 1)..combo.len() {
                let v = schema.var_of_tuple(&[combo[i], combo[j]]);
                // (1 − x_v) = 1 + (p-1)·x_v
                let mut f = BTreeMap::new();
                f.insert(Monomial::one(), 1u8);
                f.insert(Monomial::single(v), prime - 1);
                factors.push(PolyP {
                    p: prime,
                    terms: f,
                });
            }
        }
        let mut acc = PolyP::one(prime);
        for f in &factors {
            acc = acc.mul(f);
        }
        axioms.push(acc);
    }

    (schema, axioms)
}

fn combinations(n: u32, k: usize) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    let vals: Vec<u32> = (1..=n).collect();
    fn rec(
        vals: &[u32],
        start: usize,
        k_left: usize,
        chosen: &mut Vec<u32>,
        out: &mut Vec<Vec<u32>>,
    ) {
        if k_left == 0 {
            out.push(chosen.clone());
            return;
        }
        if vals.len() - start < k_left {
            return;
        }
        for i in start..vals.len() {
            chosen.push(vals[i]);
            rec(vals, i + 1, k_left - 1, chosen, out);
            chosen.pop();
        }
    }
    let mut chosen = Vec::with_capacity(k);
    rec(&vals, 0, k, &mut chosen, &mut out);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn php_functional_axiom_counts() {
        let (_, axioms) = php_functional(5, 4, 7);
        // 5 pigeon totalities + 4 holes × C(5,2)=10 AMOs = 5 + 40 = 45.
        assert_eq!(axioms.len(), 45);
    }

    #[test]
    fn ramsey_33_k6_axiom_counts() {
        // R(3,3) on K_6: C(6, 3) = 20 red bans + 20 blue bans = 40.
        let (_, axioms) = ramsey_disjunctive(3, 3, 6, 2);
        assert_eq!(axioms.len(), 40);
    }
}
