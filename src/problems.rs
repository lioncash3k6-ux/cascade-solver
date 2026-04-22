//! Problem-family factories.
//!
//! Each factory returns `(TupleVarSchema, Vec<PolyP>)`: the variable-tuple
//! schema describing how variables correspond to structured tuples, and a
//! list of polynomial axioms over 𝔽_p encoding the problem. The orbit-reduced
//! NS engine in [`crate::algebra::orbit_ns`] is problem-agnostic; all
//! problem-specific logic lives here.

use crate::algebra::ns_fp::PolyP;
use crate::algebra::poly::Monomial;
use crate::tuple_schema::{BaseSet, Generator, GroupSpec, TupleKind, TupleVarSchema};
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

/// Ramsey R(s, t) on K_n with **symmetry-breaking linear axioms** added.
///
/// Research probe: does fixing `k` disjoint edges to red (linear axioms
/// `x_{e_i} − 1 = 0`) lower the NS closing degree of the *slice* relative
/// to the unrestricted instance?
///
/// The edges are `{0,1}, {2,3}, ..., {2k-2, 2k-1}` (vertices 0-indexed from
/// the S_n base 1..=n in tuple_schema). Requires `2k ≤ n`.
///
/// Breaks `S_n` symmetry. Use `--alg-no-orbit` (dense NS) or construct a
/// stabilizer-subgroup generator set for orbit reduction; the default
/// `schema.generators()` will panic in closure check.
///
/// Proves UNSAT of the slice only (edges `e_1..e_k` all red). Full-instance
/// UNSAT requires a case-split cover or a color-swap symmetry argument.
pub fn ramsey_sbp_fix_k_edges(
    s: u32,
    t: u32,
    n: u32,
    k: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(
        2 * k <= n,
        "ramsey_sbp_fix_k_edges: need 2k ≤ n (got k={}, n={})",
        k,
        n
    );
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    // Fix k disjoint edges to red: x_{2i-1, 2i} − 1 = 0 for i = 1..=k.
    // (tuple_schema uses 1-indexed vertices.)
    for i in 0..k {
        let u = 2 * i + 1;
        let v = 2 * i + 2;
        let var_id = schema.var_of_tuple(&[u, v]);
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        terms.insert(Monomial::single(var_id), 1);
        terms.insert(Monomial::one(), prime - 1); // −1 mod p
        axioms.push(PolyP { p: prime, terms });
    }
    (schema, axioms)
}

/// Ramsey R(s, t) on K_n with the **entire neighborhood of vertex 1 fixed**:
/// edges `{1,2}..{1,r+1}` red (r_deg = r), edges `{1,r+2}..{1,n}` blue.
/// Stabilizer is `{1} × S_r × S_{n-1-r}` (permute red neighbors + blue
/// neighbors independently, vertex 1 fixed).
pub fn ramsey_sbp_full_nbhd(
    s: u32,
    t: u32,
    n: u32,
    r: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(r + 1 <= n);
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    // Red edges: 1-j for j in 2..=r+1.
    for j in 2..=(r + 1) {
        let var_id = schema.var_of_tuple(&[1, j]);
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        terms.insert(Monomial::single(var_id), 1);
        terms.insert(Monomial::one(), prime - 1);
        axioms.push(PolyP { p: prime, terms });
    }
    // Blue edges: 1-j for j in r+2..=n.
    for j in (r + 2)..=n {
        let var_id = schema.var_of_tuple(&[1, j]);
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        terms.insert(Monomial::single(var_id), 1);
        axioms.push(PolyP { p: prime, terms });
    }
    (schema, axioms)
}

/// Stabilizer generators for `ramsey_sbp_full_nbhd(s, t, n, r)`:
/// `{1} × S_r × S_{n-1-r}`.
pub fn ramsey_full_nbhd_stabilizer_gens(n: u32, r: u32) -> Vec<Generator> {
    assert!(r + 1 <= n);
    let n_us = n as usize;
    let r_us = r as usize;
    let mut gens: Vec<Generator> = Vec::new();
    // S_r on red neighbors {2..=r+1}: positions 1..r (0-indexed).
    for i in 1..r_us {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    // S_{n-1-r} on blue neighbors {r+2..=n}: positions r+1..n-1.
    for i in (r_us + 1)..n_us.saturating_sub(1) {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    gens
}

/// Ramsey R(s, t) on K_n with a **blue star of degree k at vertex 1** fixed
/// (edges `{1,2}..{1,k+1}` all blue, i.e. `x_{1,j} = 0`).
pub fn ramsey_sbp_blue_star(
    s: u32,
    t: u32,
    n: u32,
    k: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(k + 1 <= n);
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    for j in 2..=(k + 1) {
        let var_id = schema.var_of_tuple(&[1, j]);
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        terms.insert(Monomial::single(var_id), 1);
        axioms.push(PolyP { p: prime, terms });
    }
    (schema, axioms)
}

/// Ramsey R(s, t) on K_n with a **red star of degree k at vertex 1** fixed.
/// Edges `{1,2}, {1,3}, ..., {1, k+1}` all red. For `k ≥ 2`, this constrains
/// vertex 1's red-neighborhood without (by itself) forcing any K_3.
pub fn ramsey_sbp_red_star(
    s: u32,
    t: u32,
    n: u32,
    k: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(k + 1 <= n);
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    for j in 2..=(k + 1) {
        let var_id = schema.var_of_tuple(&[1, j]);
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        terms.insert(Monomial::single(var_id), 1);
        terms.insert(Monomial::one(), prime - 1);
        axioms.push(PolyP { p: prime, terms });
    }
    (schema, axioms)
}

/// Ramsey R(s, t) on K_n with **a fixed red K_m clique** added as SBP axioms.
/// For `m ≥ s`, the red-clique ban immediately contradicts ⇒ degree-3
/// closure. Useful as a "trivial sanity" end of the SBP-strength axis.
pub fn ramsey_sbp_red_clique(
    s: u32,
    t: u32,
    n: u32,
    m: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(m <= n);
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    // Fix every edge inside K_m on vertices {1..=m} to red.
    for u in 1..=m {
        for v in (u + 1)..=m {
            let var_id = schema.var_of_tuple(&[u, v]);
            let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
            terms.insert(Monomial::single(var_id), 1);
            terms.insert(Monomial::one(), prime - 1);
            axioms.push(PolyP { p: prime, terms });
        }
    }
    (schema, axioms)
}

/// Ramsey R(s, t) on K_n with a **S_n-invariant linear slice** added:
/// `(∑_e x_e) − r = 0`. Restricts to assignments with exactly `r` red edges.
///
/// Unlike [`ramsey_sbp_fix_k_edges`], this axiom IS S_n-invariant, so the
/// full `schema.generators()` work — no stabilizer needed. Control for
/// "does adding any linear axiom drop NS degree, or is the SBP structure
/// specifically doing the work?"
pub fn ramsey_slice_edge_count(
    s: u32,
    t: u32,
    n: u32,
    r: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    let (schema, mut axioms) = ramsey_disjunctive(s, t, n, prime);
    // Add axiom (∑_e x_e) − r = 0 (mod p).
    let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
    for u in 1..=n {
        for v in (u + 1)..=n {
            let var_id = schema.var_of_tuple(&[u, v]);
            terms.insert(Monomial::single(var_id), 1);
        }
    }
    // Constant term: −r mod p.
    let neg_r = ((prime as u32) - (r % prime as u32)) % prime as u32;
    if neg_r != 0 {
        terms.insert(Monomial::one(), neg_r as u8);
    }
    axioms.push(PolyP { p: prime, terms });
    (schema, axioms)
}

/// Stabilizer-subgroup generators for `ramsey_sbp_red_star(s, t, n, k)`.
/// Fixing k red edges all incident to vertex 1: stabilizer = {1} × S_k × S_{n−k−1}.
pub fn ramsey_redstar_stabilizer_gens(n: u32, k: u32) -> Vec<Generator> {
    assert!(k + 1 <= n);
    let n_us = n as usize;
    let k_us = k as usize;
    let mut gens: Vec<Generator> = Vec::new();
    // S_k on leaves {2..=k+1}: positions 1..k (0-indexed).
    for i in 1..k_us {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    // S_{n-k-1} on remaining {k+2..=n}: positions k+1..n-1.
    for i in (k_us + 1)..n_us.saturating_sub(1) {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    gens
}

/// Stabilizer-subgroup generators for `ramsey_sbp_red_clique(s, t, n, m)`.
/// The clique on vertices `{1..=m}` has setwise stabilizer `S_m × S_{n−m}`.
pub fn ramsey_redclique_stabilizer_gens(n: u32, m: u32) -> Vec<Generator> {
    assert!(m <= n);
    let n_us = n as usize;
    let m_us = m as usize;
    let mut gens: Vec<Generator> = Vec::new();
    // S_m on {1..=m}: adjacent transpositions (positions 0..m-1).
    for i in 0..m_us.saturating_sub(1) {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    // S_{n−m} on {m+1..=n}: adjacent transpositions (positions m..n-1).
    for i in m_us..n_us.saturating_sub(1) {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    gens
}

/// Stabilizer-subgroup generators for `ramsey_sbp_fix_k_edges(s, t, n, k)`.
///
/// The SBP fixes edges `{2i−1, 2i}` for `i = 1..=k` (1-indexed vertices).
/// Its setwise stabilizer in `S_n` is generated by:
///
/// * For each fixed edge, the internal swap of its two vertices.
/// * Adjacent transpositions among the remaining `n − 2k` free vertices
///   `{2k+1, 2k+2, ..., n}`.
///
/// This generates `(S_2)^k × S_{n−2k}` (a proper subgroup of `S_n`). The
/// SBP axiom set is setwise closed under this group: each edge axiom
/// `x_{2i-1, 2i} − 1` is fixed by its internal swap, and the free-vertex
/// transpositions move only variables disjoint from the SBP edges.
///
/// Missing from this generator set: the "swap two SBP edges" wreath action
/// (permuting the list of fixed edges). Adding it would require a swap
/// of `{vertex 2i−1, vertex 2i}` with `{vertex 2j−1, vertex 2j}`
/// simultaneously — not an adjacent transposition, so a separate generator.
/// Omitted for now; not needed for the experiments at hand.
pub fn ramsey_sbp_stabilizer_gens(n: u32, k: u32) -> Vec<Generator> {
    assert!(2 * k <= n);
    let n_us = n as usize;
    let mut gens: Vec<Generator> = Vec::new();
    // Internal swap of each fixed edge: positions 2i, 2i+1 (0-indexed).
    for i in 0..k as usize {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(2 * i, 2 * i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    // Adjacent transpositions among free vertices: positions 2k..n−1.
    let start = 2 * k as usize;
    for i in start..n_us.saturating_sub(1) {
        let mut p: Vec<u32> = (0..n).collect();
        p.swap(i, i + 1);
        gens.push(Generator { perms: vec![p] });
    }
    gens
}

/// Count_q / modular counting principle on the complete q-uniform hypergraph.
///
/// Instance: partition `[n]` into q-sized blocks. UNSAT iff `q ∤ n`.
///
/// * Schema: k-subsets of `[n]` (one base), `k = q`.
/// * Group: `S_n` acting diagonally on vertices (hence on q-subsets).
/// * Axioms: for each vertex `v`, `(∑_{S ∋ v} x_S) − 1 = 0` — vertex `v`
///   is in exactly one chosen q-subset.
///
/// Characteristic sensitivity (the reason this family is in the solver):
///
/// * Over `𝔽_p` with `p ∣ q`: degree-1 refutation — summing all vertex
///   axioms gives `q · ∑_S x_S − n = 0 ≡ −n (mod p)`, nonzero iff `p ∤ n`.
/// * Over `𝔽_p` with `p ∤ q`: NS degree grows; exact scaling is the
///   empirical question this family exists to answer.
pub fn count_q_partition(
    n: u32,
    q: u32,
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(q >= 2, "count_q_partition: q must be >= 2 (got {})", q);
    assert!(n >= q, "count_q_partition: n must be >= q (got n={}, q={})", n, q);

    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedSubset { size: q },
        group: GroupSpec::Diagonal,
    };

    let mut axioms: Vec<PolyP> = Vec::new();

    // For each vertex v: axiom = (∑_{S ∋ v} x_S) − 1.
    //
    // Enumerate q-subsets containing v by choosing the other (q-1) elements
    // from [n] \ {v}.
    for v in 1..=n {
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        let others: Vec<u32> = (1..=n).filter(|&u| u != v).collect();
        for combo in choose_from(&others, (q - 1) as usize) {
            let mut subset = combo.clone();
            subset.push(v);
            let var_id = schema.var_of_tuple(&subset);
            terms.insert(Monomial::single(var_id), 1);
        }
        terms.insert(Monomial::one(), prime - 1); // −1 mod p
        axioms.push(PolyP {
            p: prime,
            terms,
        });
    }

    (schema, axioms)
}

/// Tseitin formula on a graph `G = ([n], E)` with vertex charges `c_v ∈ {0, 1}`.
///
/// * Schema: unordered vertex pairs (all C(n, 2) pairs), `S_n` diagonal action.
/// * Axioms: for each vertex `v`, `(∑_{e ∋ v} x_e) − c_v = 0` — a linear
///   polynomial over 𝔽_p. Only edges in `E` appear; other pair-variables
///   are free and play no role.
/// * UNSAT condition (multilinear NS over 𝔽_2): `∑_v c_v` is odd. Proof is
///   the handshake lemma in cert form.
///
/// Closure: the axiom set is `Aut(G)`-closed by construction, and `Aut(G)`
/// is generally a *proper* subgroup of `S_n` (e.g. cycle `C_n` preserved
/// only by the dihedral group, not by all transpositions). For full orbit
/// reduction use [`crate::algebra::orbit_ns::find_orbit_cert_fp_with_gens`]
/// with `Aut(G)` generators; the schema's default `S_n` generators will
/// break closure and panic unless the graph is edge-transitive under `S_n`
/// (only `K_n`).
///
/// For Tseitin over 𝔽_2, orbit reduction never helps (`2 ∣ |G|` for any
/// non-trivial symmetry group) and the dense engine
/// [`crate::algebra::ns_fp::find_ns_p_from_axioms`] is the intended path.
/// This factory still produces the schema so the engine interface stays
/// uniform across families.
pub fn tseitin_graph(
    n_verts: u32,
    edges: &[(u32, u32)],
    charges: &[u8],
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    assert_eq!(
        charges.len(),
        n_verts as usize,
        "tseitin_graph: charges.len() must equal n_verts"
    );
    assert!(
        prime >= 2,
        "tseitin_graph: prime must be ≥ 2 (got {})",
        prime
    );

    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n_verts)],
        tuple_kind: TupleKind::UnorderedPair,
        group: GroupSpec::Diagonal,
    };

    // Per-vertex incidence list.
    let mut incidence: Vec<Vec<u32>> = vec![Vec::new(); (n_verts + 1) as usize];
    for &(u, v) in edges {
        assert!(u >= 1 && u <= n_verts && v >= 1 && v <= n_verts && u != v);
        let var_id = schema.var_of_tuple(&[u, v]);
        incidence[u as usize].push(var_id);
        incidence[v as usize].push(var_id);
    }

    let mut axioms: Vec<PolyP> = Vec::new();
    for v in 1..=n_verts {
        let mut terms: BTreeMap<Monomial, u8> = BTreeMap::new();
        for &var_id in &incidence[v as usize] {
            terms.insert(Monomial::single(var_id), 1);
        }
        // −c_v mod p.
        let cv = charges[(v - 1) as usize] % prime;
        let neg_cv = (prime - cv) % prime;
        if neg_cv != 0 {
            terms.insert(Monomial::one(), neg_cv);
        }
        axioms.push(PolyP {
            p: prime,
            terms,
        });
    }

    (schema, axioms)
}

/// Tseitin on the complete graph `K_n` with uniform charge `c`.
///
/// For `c == 1` this coincides with the perfect-matching principle
/// `PM_n` and with [`count_q_partition`]`(n, 2, prime)`. Provided as a
/// convenience alias that makes the Tseitin framing explicit.
pub fn tseitin_kn(n: u32, charge: u8, prime: u8) -> (TupleVarSchema, Vec<PolyP>) {
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for i in 1..n {
        for j in (i + 1)..=n {
            edges.push((i, j));
        }
    }
    let charges = vec![charge; n as usize];
    tseitin_graph(n, &edges, &charges, prime)
}

/// Tseitin on the cycle `C_n` with uniform charge `c`.
///
/// Same UNSAT condition as `K_n` (`∑ c_v = n·c` odd), but a *different*
/// degree curve because the incidence graph is much sparser. Useful
/// empirical contrast: does the Tseitin NS degree depend on graph
/// topology, or only on `(n, charge)`?
pub fn tseitin_cycle(n: u32, charge: u8, prime: u8) -> (TupleVarSchema, Vec<PolyP>) {
    assert!(n >= 3, "tseitin_cycle requires n >= 3 (got {})", n);
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for i in 1..n {
        edges.push((i, i + 1));
    }
    edges.push((1, n));
    let charges = vec![charge; n as usize];
    tseitin_graph(n, &edges, &charges, prime)
}

/// Tseitin on the Petersen graph with uniform charge.
///
/// The Petersen graph: 10 vertices, 15 edges, 3-regular. `Aut(Petersen) = S_5`
/// acting on 10 = `C(5, 2)` vertex labels indexed by 2-subsets of `[5]`.
/// Uniform charge 1 gives `∑ c_v = 10 = even → SAT` over 𝔽_2; uniform charge
/// pattern has to be broken for UNSAT. Provided here as infrastructure so
/// one can experiment with non-uniform charges.
pub fn tseitin_petersen(
    charges: &[u8; 10],
    prime: u8,
) -> (TupleVarSchema, Vec<PolyP>) {
    // Standard Petersen: outer 5-cycle 1-2-3-4-5-1, inner 5-cycle 6-8-10-7-9-6,
    // and spokes 1-6, 2-7, 3-8, 4-9, 5-10.
    let edges: [(u32, u32); 15] = [
        (1, 2), (2, 3), (3, 4), (4, 5), (5, 1),       // outer
        (6, 8), (8, 10), (10, 7), (7, 9), (9, 6),     // inner
        (1, 6), (2, 7), (3, 8), (4, 9), (5, 10),      // spokes
    ];
    tseitin_graph(10, &edges, charges, prime)
}

fn choose_from(src: &[u32], k: usize) -> Vec<Vec<u32>> {
    let mut out = Vec::new();
    fn rec(
        src: &[u32],
        start: usize,
        k_left: usize,
        chosen: &mut Vec<u32>,
        out: &mut Vec<Vec<u32>>,
    ) {
        if k_left == 0 {
            out.push(chosen.clone());
            return;
        }
        if src.len() - start < k_left {
            return;
        }
        for i in start..src.len() {
            chosen.push(src[i]);
            rec(src, i + 1, k_left - 1, chosen, out);
            chosen.pop();
        }
    }
    let mut chosen = Vec::with_capacity(k);
    rec(src, 0, k, &mut chosen, &mut out);
    out
}

// ─────────────────────────────────────────────────────────────────────
// SAT model finders (Option A — per-family closed-form SAT detection)
// ─────────────────────────────────────────────────────────────────────
//
// For each factory above we know the SAT/UNSAT boundary in closed form:
//
//   php_functional(P, H)    SAT iff P ≤ H
//   count_q_partition(n,q)  SAT iff q ∣ n
//   tseitin_graph(...)      SAT iff ∑_v c_v is even
//
// These `*_model` functions return `Some(Vec<bool>)` with a satisfying
// variable assignment (indexed as `model[var_id - 1]`) when the instance
// is SAT, and `None` when it is UNSAT. The assignment is consistent with
// the *same* variable numbering the corresponding factory produces, so a
// caller can verify against those axioms.

/// Satisfying assignment for PHP_{P, H} when `P ≤ H`.
///
/// Strategy: the injection `pigeon i → hole i` uses `P` distinct holes
/// and satisfies both the totality (each pigeon maps somewhere) and
/// the AMO (no two pigeons share a hole) axioms.
pub fn php_functional_model(n_pigeons: u32, n_holes: u32) -> Option<Vec<bool>> {
    if n_pigeons > n_holes {
        return None;
    }
    let schema = TupleVarSchema {
        bases: vec![
            BaseSet::new("P", n_pigeons),
            BaseSet::new("H", n_holes),
        ],
        tuple_kind: TupleKind::Ordered,
        group: GroupSpec::FullProduct,
    };
    let mut model = vec![false; schema.n_vars() as usize];
    for p in 1..=n_pigeons {
        let v = schema.var_of_tuple(&[p, p]); // pigeon p → hole p
        model[(v - 1) as usize] = true;
    }
    Some(model)
}

/// Satisfying assignment for `count_q_partition(n, q)` when `q ∣ n`.
///
/// Strategy: the natural block partition `{1..q}, {q+1..2q}, ..., {n−q+1..n}`.
/// Each vertex is in exactly one chosen block, so every vertex axiom is
/// satisfied.
pub fn count_q_partition_model(n: u32, q: u32) -> Option<Vec<bool>> {
    if q == 0 || n % q != 0 {
        return None;
    }
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedSubset { size: q },
        group: GroupSpec::Diagonal,
    };
    let mut model = vec![false; schema.n_vars() as usize];
    for block in 0..(n / q) {
        let start = block * q + 1;
        let subset: Vec<u32> = (start..start + q).collect();
        let v = schema.var_of_tuple(&subset);
        model[(v - 1) as usize] = true;
    }
    Some(model)
}

/// Satisfying assignment for `tseitin_graph(n, edges, charges)` when
/// `∑_v c_v` is even.
///
/// Strategy: Gaussian elimination over 𝔽_2 on the vertex-edge incidence
/// system `M · x = c`, where `M[v][e] = 1` iff `v` is incident to `e`.
/// Any particular solution works; we take the one produced by
/// back-substitution (free variables set to 0).
///
/// Complexity: `O(|V|² · |E|)` for the elimination. Fine for graphs of
/// practical interest (K_n up to `n = 16`, hypercubes up to `Q_4`, etc.).
pub fn tseitin_graph_model(
    n_verts: u32,
    edges: &[(u32, u32)],
    charges: &[u8],
) -> Option<Vec<bool>> {
    assert_eq!(
        charges.len(),
        n_verts as usize,
        "tseitin_graph_model: charges.len() must equal n_verts"
    );
    let parity_sum: u32 = charges.iter().map(|&c| (c & 1) as u32).sum();
    if parity_sum % 2 != 0 {
        return None; // handshake lemma — UNSAT
    }
    let n_edges = edges.len();
    let n = n_verts as usize;

    // Augmented incidence matrix: rows = vertices, cols = edges + 1 RHS.
    // Each row is a bitset over n_edges + 1 bits. Using `Vec<u64>` words.
    let n_cols = n_edges + 1;
    let words = (n_cols + 63) / 64;
    let mut rows: Vec<Vec<u64>> = vec![vec![0u64; words]; n];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        let w = e_idx / 64;
        let b = 1u64 << (e_idx & 63);
        rows[(u - 1) as usize][w] ^= b;
        rows[(v - 1) as usize][w] ^= b;
    }
    // RHS column = n_edges.
    let rhs_w = n_edges / 64;
    let rhs_b = 1u64 << (n_edges & 63);
    for (v_idx, &c) in charges.iter().enumerate() {
        if c & 1 != 0 {
            rows[v_idx][rhs_w] ^= rhs_b;
        }
    }

    // Forward elimination. For each edge column in order, find a pivot
    // row and XOR it into every other row with that column set.
    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; n_edges];
    let mut next_pivot_row = 0usize;
    for col in 0..n_edges {
        let w = col / 64;
        let b = 1u64 << (col & 63);
        let mut pivot: Option<usize> = None;
        for r in next_pivot_row..n {
            if rows[r][w] & b != 0 {
                pivot = Some(r);
                break;
            }
        }
        let pivot = match pivot {
            Some(r) => r,
            None => continue,
        };
        rows.swap(pivot, next_pivot_row);
        let prow = next_pivot_row;
        for r in 0..n {
            if r == prow {
                continue;
            }
            if rows[r][w] & b != 0 {
                // rows[r] ^= rows[prow]
                for k in 0..words {
                    rows[r][k] ^= rows[prow][k];
                }
            }
        }
        pivot_row_of_col[col] = Some(prow);
        next_pivot_row += 1;
    }

    // Consistency check: any all-zero row with RHS = 1 is a contradiction.
    for r in 0..n {
        let lhs_zero = (0..n_edges).all(|c| {
            let w = c / 64;
            let b = 1u64 << (c & 63);
            rows[r][w] & b == 0
        });
        if lhs_zero && (rows[r][rhs_w] & rhs_b != 0) {
            return None;
        }
    }

    // Back-substitute: free variables (no pivot) are 0; pivot variables
    // take the value of the RHS in their row.
    let mut model = vec![false; n_edges];
    for col in 0..n_edges {
        if let Some(prow) = pivot_row_of_col[col] {
            let bit_set = rows[prow][rhs_w] & rhs_b != 0;
            model[col] = bit_set;
        }
    }
    Some(model)
}

/// Convenience wrapper matching [`tseitin_kn`]'s variable numbering.
pub fn tseitin_kn_model(n: u32, charge: u8) -> Option<Vec<bool>> {
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for i in 1..n {
        for j in (i + 1)..=n {
            edges.push((i, j));
        }
    }
    let charges = vec![charge; n as usize];
    // tseitin_kn uses UnorderedPair schema; `tseitin_graph_model` indexes
    // model entries by edge position in `edges`, matching
    // `schema.var_of_tuple(&[u, v])` lex numbering. Map them explicitly.
    let raw = tseitin_graph_model(n, &edges, &charges)?;
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedPair,
        group: GroupSpec::Diagonal,
    };
    let mut model = vec![false; schema.n_vars() as usize];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        let var = schema.var_of_tuple(&[u, v]);
        model[(var - 1) as usize] = raw[e_idx];
    }
    Some(model)
}

/// Convenience wrapper matching [`tseitin_cycle`]'s variable numbering.
pub fn tseitin_cycle_model(n: u32, charge: u8) -> Option<Vec<bool>> {
    assert!(n >= 3);
    let mut edges: Vec<(u32, u32)> = Vec::new();
    for i in 1..n {
        edges.push((i, i + 1));
    }
    edges.push((1, n));
    let charges = vec![charge; n as usize];
    let raw = tseitin_graph_model(n, &edges, &charges)?;
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedPair,
        group: GroupSpec::Diagonal,
    };
    let mut model = vec![false; schema.n_vars() as usize];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        let var = schema.var_of_tuple(&[u, v]);
        model[(var - 1) as usize] = raw[e_idx];
    }
    Some(model)
}

/// Convenience wrapper matching [`tseitin_petersen`]'s variable numbering.
pub fn tseitin_petersen_model(charges: &[u8; 10]) -> Option<Vec<bool>> {
    let edges: [(u32, u32); 15] = [
        (1, 2), (2, 3), (3, 4), (4, 5), (5, 1),
        (6, 8), (8, 10), (10, 7), (7, 9), (9, 6),
        (1, 6), (2, 7), (3, 8), (4, 9), (5, 10),
    ];
    let raw = tseitin_graph_model(10, &edges, charges)?;
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", 10)],
        tuple_kind: TupleKind::UnorderedPair,
        group: GroupSpec::Diagonal,
    };
    let mut model = vec![false; schema.n_vars() as usize];
    for (e_idx, &(u, v)) in edges.iter().enumerate() {
        let var = schema.var_of_tuple(&[u, v]);
        model[(var - 1) as usize] = raw[e_idx];
    }
    Some(model)
}

// ─────────────────────────────────────────────────────────────────────

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

    #[test]
    fn count_q_partition_shape() {
        // Count_3 on [7]: C(7,3) = 35 variables, 7 vertex axioms.
        let (schema, axioms) = count_q_partition(7, 3, 5);
        assert_eq!(schema.n_vars(), 35);
        assert_eq!(axioms.len(), 7);
        // Each vertex axiom has C(6, 2) = 15 q-subsets containing it, plus
        // the constant term.
        for a in &axioms {
            assert_eq!(a.terms.len(), 15 + 1);
        }
    }

    #[test]
    fn tseitin_kn_shape() {
        // Tseitin on K_5 with charge 1: 5 vertex axioms; each axiom has
        // 4 edge vars + 1 constant term. Equivalent as a formula (up to
        // variable relabeling) to count_q_partition(5, 2) — the Tseitin
        // alias uses UnorderedPair's lex numbering while count_q uses
        // UnorderedSubset's colex numbering.
        let (schema, axioms) = tseitin_kn(5, 1, 7);
        assert_eq!(schema.n_vars(), 10); // C(5, 2)
        assert_eq!(axioms.len(), 5);
        for a in &axioms {
            assert_eq!(a.terms.len(), 5); // 4 vars + 1 constant
            assert_eq!(*a.terms.get(&Monomial::one()).unwrap(), 6u8); // −1 mod 7
        }
    }

    #[test]
    fn tseitin_cycle_charges_appear_as_constant_terms() {
        let (_, axioms) = tseitin_cycle(5, 1, 7);
        assert_eq!(axioms.len(), 5);
        // Each vertex has exactly 2 incident edges + a constant −1 = 6 mod 7.
        for a in &axioms {
            assert_eq!(a.terms.len(), 3);
            assert_eq!(*a.terms.get(&Monomial::one()).unwrap(), 6u8);
        }
    }

    #[test]
    fn tseitin_petersen_structure() {
        let charges = [1u8; 10];
        let (schema, axioms) = tseitin_petersen(&charges, 2);
        assert_eq!(schema.n_vars(), 45); // C(10, 2)
        assert_eq!(axioms.len(), 10);
        // Petersen is 3-regular so each vertex axiom = 3 edge vars + (−1 mod 2 = 1).
        for a in &axioms {
            assert_eq!(a.terms.len(), 4);
        }
    }

    #[test]
    fn count_q_partition_axioms_closed_under_group() {
        // Closure is the precondition for orbit_ns to succeed (it panics
        // otherwise). Spot-check via the first adjacent-transposition
        // generator.
        let (schema, axioms) = count_q_partition(6, 2, 3);
        let gens = schema.generators();
        // Build a canonical key → axiom index table.
        let mut key_of: BTreeMap<Vec<(Monomial, u8)>, usize> = BTreeMap::new();
        for (i, a) in axioms.iter().enumerate() {
            let mut v: Vec<(Monomial, u8)> = a.terms.iter().map(|(m, c)| (m.clone(), *c)).collect();
            v.sort();
            key_of.insert(v, i);
        }
        // Apply g to each axiom; the image must be an axiom.
        let g = &gens[0];
        for a in &axioms {
            let mut img: BTreeMap<Monomial, u8> = BTreeMap::new();
            for (m, c) in &a.terms {
                let m_img = schema.apply_mono(m, g);
                let e = img.entry(m_img).or_insert(0);
                *e = (*e + c) % a.p;
            }
            let mut v: Vec<(Monomial, u8)> = img.into_iter().collect();
            v.sort();
            assert!(key_of.contains_key(&v), "axiom image not in axiom set");
        }
    }

    // ─────────────────────────────────────────────────────────────────
    // SAT model finder tests — each one checks that the model actually
    // satisfies the polynomial axioms produced by the paired factory.
    // ─────────────────────────────────────────────────────────────────

    /// Evaluate a polynomial over 𝔽_p at a Boolean assignment; return the
    /// integer residue mod p. Used by the model-check tests below.
    fn eval_polyp(poly: &PolyP, model: &[bool]) -> u8 {
        let mut acc: u16 = 0;
        for (m, &c) in &poly.terms {
            let ok = m.0.iter().all(|&v| model[(v - 1) as usize]);
            if ok {
                acc = (acc + c as u16) % poly.p as u16;
            }
        }
        acc as u8
    }

    #[test]
    fn php_model_unsat_when_p_gt_h() {
        assert!(php_functional_model(5, 4).is_none());
        assert!(php_functional_model(3, 2).is_none());
    }

    #[test]
    fn php_model_satisfies_axioms_when_p_le_h() {
        for (p_, h) in [(3, 3), (3, 5), (5, 5), (4, 7)] {
            let model = php_functional_model(p_, h).expect("SAT");
            let (_, axioms) = php_functional(p_, h, 7);
            for (i, a) in axioms.iter().enumerate() {
                assert_eq!(
                    eval_polyp(a, &model),
                    0,
                    "PHP_{{{}, {}}}: axiom {} not satisfied",
                    p_, h, i
                );
            }
        }
    }

    #[test]
    fn count_q_model_unsat_when_not_divisible() {
        assert!(count_q_partition_model(5, 3).is_none());
        assert!(count_q_partition_model(7, 2).is_none());
        assert!(count_q_partition_model(4, 3).is_none());
    }

    #[test]
    fn count_q_model_satisfies_axioms_when_divisible() {
        for (n, q) in [(4, 2), (6, 2), (6, 3), (9, 3), (8, 4)] {
            let model = count_q_partition_model(n, q).expect("SAT");
            let (_, axioms) = count_q_partition(n, q, 5);
            for (i, a) in axioms.iter().enumerate() {
                assert_eq!(
                    eval_polyp(a, &model),
                    0,
                    "Count_{} n={}: axiom {} not satisfied",
                    q, n, i
                );
            }
        }
    }

    #[test]
    fn tseitin_kn_model_unsat_when_sum_odd() {
        // charge 1 on n odd → ∑ c_v = n odd → UNSAT
        assert!(tseitin_kn_model(5, 1).is_none());
        assert!(tseitin_kn_model(7, 1).is_none());
    }

    #[test]
    fn tseitin_kn_model_satisfies_axioms_when_sum_even() {
        // n even with charge 1 → SAT
        for n in [4u32, 6, 8] {
            let model = tseitin_kn_model(n, 1).expect("SAT");
            let (_, axioms) = tseitin_kn(n, 1, 2);
            for (i, a) in axioms.iter().enumerate() {
                assert_eq!(
                    eval_polyp(a, &model),
                    0,
                    "Tseitin K_{} charge=1: axiom {} not satisfied",
                    n, i
                );
            }
        }
        // n odd with charge 0 → SAT (all-zero model)
        for n in [5u32, 7] {
            let model = tseitin_kn_model(n, 0).expect("SAT");
            let (_, axioms) = tseitin_kn(n, 0, 2);
            for (i, a) in axioms.iter().enumerate() {
                assert_eq!(
                    eval_polyp(a, &model),
                    0,
                    "Tseitin K_{} charge=0: axiom {} not satisfied",
                    n, i
                );
            }
        }
    }

    #[test]
    fn tseitin_cycle_model_satisfies_axioms() {
        // Even-cycle with charge 1 → SAT
        let model = tseitin_cycle_model(6, 1).expect("SAT");
        let (_, axioms) = tseitin_cycle(6, 1, 2);
        for (i, a) in axioms.iter().enumerate() {
            assert_eq!(eval_polyp(a, &model), 0, "C_6 axiom {} not satisfied", i);
        }
    }

    #[test]
    fn tseitin_petersen_uniform_charge_1_is_sat() {
        // ∑ c_v = 10 (even) → SAT (consistent with README note).
        let charges = [1u8; 10];
        let model = tseitin_petersen_model(&charges).expect("SAT");
        let (_, axioms) = tseitin_petersen(&charges, 2);
        for (i, a) in axioms.iter().enumerate() {
            assert_eq!(
                eval_polyp(a, &model),
                0,
                "Petersen axiom {} not satisfied",
                i
            );
        }
    }
}
