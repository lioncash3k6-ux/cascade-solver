//! Canonical labeling and orbit enumeration for edge-sets of K_n under S_n.
//!
//! Used by the orbit-NS engine to replace the O(C(n²,d)) monomial BFS with
//! direct enumeration of O(1) orbit representatives.
//!
//! # Key facts
//!
//! * A degree-d edge-set monomial in K_n is an orbit-representative iff it
//!   is the lex-minimum labeling of its isomorphism class.
//! * Each connected component of d edges has ≤ d+1 vertices (tree bound), so
//!   each component has ≤ 8 vertices for d ≤ 7. Brute-force k! canonical
//!   labeling is feasible for k ≤ 8 (8! = 40 320).
//! * orbit_size = P(n, k) / |Aut(H)| where k = number of active vertices in
//!   the canonical graph H and |Aut(H)| is the automorphism group size.

/// A canonical simple graph on vertices 0..n_verts−1.
/// Edges stored as sorted (u, v) pairs with u < v, packed as `(u << 4) | v`
/// (both u, v fit in 4 bits since max vertices = 14 = 2 × 7 edges).
/// The edge list is the lex-minimum over all vertex relabelings.
#[derive(Clone, PartialEq, Eq, Hash, PartialOrd, Ord, Debug, Default)]
pub(crate) struct CanonGraph {
    pub n_verts: u8,
    pub n_edges: u8,
    pub edges: [u8; 7], // packed: (u << 4) | v, up to 7 edges
}

impl CanonGraph {
    pub fn empty() -> Self {
        Self::default()
    }

    fn from_sorted_edges(edges: &[(u8, u8)]) -> Self {
        debug_assert!(edges.len() <= 7);
        let n_verts = edges
            .iter()
            .flat_map(|&(u, v)| [u, v])
            .max()
            .map(|m| m + 1)
            .unwrap_or(0);
        let mut g = Self::default();
        g.n_verts = n_verts;
        g.n_edges = edges.len() as u8;
        for (i, &(u, v)) in edges.iter().enumerate() {
            g.edges[i] = (u << 4) | v;
        }
        g
    }

    pub fn edge_iter(&self) -> impl Iterator<Item = (u8, u8)> + '_ {
        self.edges[..self.n_edges as usize]
            .iter()
            .map(|&e| (e >> 4, e & 0x0f))
    }
}

// ---------------------------------------------------------------------------
// Canonical form
// ---------------------------------------------------------------------------

/// Advance a permutation to the next one in lex order. Returns false when
/// already at the last permutation.
fn next_perm(v: &mut [u8]) -> bool {
    let n = v.len();
    if n <= 1 {
        return false;
    }
    let mut i = n - 1;
    while i > 0 && v[i - 1] >= v[i] {
        i -= 1;
    }
    if i == 0 {
        return false;
    }
    let mut j = n - 1;
    while v[j] <= v[i - 1] {
        j -= 1;
    }
    v.swap(i - 1, j);
    v[i..].reverse();
    true
}

/// Apply a permutation to an edge list and return sorted result.
fn relabel(edges: &[(u8, u8)], perm: &[u8]) -> Vec<(u8, u8)> {
    let mut r: Vec<(u8, u8)> = edges
        .iter()
        .map(|&(u, v)| {
            let (a, b) = (perm[u as usize], perm[v as usize]);
            if a < b { (a, b) } else { (b, a) }
        })
        .collect();
    r.sort_unstable();
    r
}

/// Brute-force canonical form for a CONNECTED graph on n_verts ≤ 8 vertices.
/// Returns the lex-minimum edge list and the automorphism group size.
fn canon_connected(edges: &[(u8, u8)], n_verts: u8) -> (Vec<(u8, u8)>, u64) {
    debug_assert!(n_verts <= 8, "brute-force canon: n_verts={} > 8", n_verts);
    let mut perm: Vec<u8> = (0..n_verts).collect();
    let mut best: Option<Vec<(u8, u8)>> = None;
    let mut aut = 0u64;
    loop {
        let r = relabel(edges, &perm);
        match &best {
            None => {
                best = Some(r.clone());
                aut = 1;
            }
            Some(b) if r < *b => {
                best = Some(r);
                aut = 1;
            }
            Some(b) if r == *b => {
                aut += 1;
            }
            _ => {}
        }
        if !next_perm(&mut perm) {
            break;
        }
    }
    (best.unwrap(), aut)
}

/// Union-find for connected components.
fn uf_find(parent: &mut Vec<u8>, x: u8) -> u8 {
    if parent[x as usize] != x {
        let p = uf_find(parent, parent[x as usize]);
        parent[x as usize] = p;
    }
    parent[x as usize]
}

fn uf_union(parent: &mut Vec<u8>, x: u8, y: u8) {
    let px = uf_find(parent, x);
    let py = uf_find(parent, y);
    if px != py {
        parent[px as usize] = py;
    }
}

/// Split an edge list on vertices 0..n_verts−1 into connected components.
/// Returns list of (component_edges, component_vertex_set).
fn split_components(edges: &[(u8, u8)], n_verts: u8) -> Vec<Vec<(u8, u8)>> {
    let mut parent: Vec<u8> = (0..n_verts).collect();
    for &(u, v) in edges {
        uf_union(&mut parent, u, v);
    }
    let mut map: std::collections::HashMap<u8, Vec<(u8, u8)>> = Default::default();
    for &(u, v) in edges {
        let root = uf_find(&mut parent, u);
        map.entry(root).or_default().push((u, v));
    }
    map.into_values().collect()
}

/// Compress vertex labels in an edge list to 0..k−1 (preserving relative order).
fn compress(edges: &[(u8, u8)]) -> (Vec<(u8, u8)>, u8) {
    let mut verts: Vec<u8> = edges.iter().flat_map(|&(u, v)| [u, v]).collect();
    verts.sort_unstable();
    verts.dedup();
    let k = verts.len() as u8;
    let lookup = |x: u8| verts.iter().position(|&v| v == x).unwrap() as u8;
    let r: Vec<(u8, u8)> = edges
        .iter()
        .map(|&(u, v)| (lookup(u), lookup(v)))
        .collect();
    (r, k)
}

/// Canonical form of an arbitrary edge list (possibly disconnected).
/// Returns (CanonGraph, automorphism_group_size).
/// The canonical form is the lex-minimum edge list over all vertex relabelings,
/// with identical components sorted and their permutations included in |Aut|.
pub(crate) fn canonicalize(edges: &[(u8, u8)]) -> (CanonGraph, u64) {
    if edges.is_empty() {
        return (CanonGraph::empty(), 1);
    }

    // Compress all vertices to 0..k−1
    let (comp_edges, k) = compress(edges);

    // Split into connected components
    let raw_comps = split_components(&comp_edges, k);

    // Canonicalize each component independently
    let mut canon_comps: Vec<(Vec<(u8, u8)>, u64)> = raw_comps
        .iter()
        .map(|c| {
            let (cc, ck) = compress(c);
            canon_connected(&cc, ck)
        })
        .collect();

    // Sort components by their canonical edge list (lex order)
    canon_comps.sort_unstable_by(|a, b| a.0.cmp(&b.0));

    // Multiply per-component |Aut| and account for permuting identical components
    let mut total_aut = 1u64;
    let mut i = 0;
    while i < canon_comps.len() {
        let mut j = i + 1;
        while j < canon_comps.len() && canon_comps[j].0 == canon_comps[i].0 {
            j += 1;
        }
        let count = (j - i) as u64;
        // Each instance contributes its own |Aut|; identical instances add (count!) swaps
        let per_aut = canon_comps[i].1;
        total_aut *= per_aut.pow(count as u32);
        // Factorial for swapping identical components
        total_aut *= (1..=count).product::<u64>();
        i = j;
    }

    // Re-assign vertex labels: component 0 → 0..k0−1, component 1 → k0..k0+k1−1, …
    let mut all_edges: Vec<(u8, u8)> = Vec::new();
    let mut offset = 0u8;
    for (c_edges, _) in &canon_comps {
        let kc = c_edges
            .iter()
            .flat_map(|&(u, v)| [u, v])
            .max()
            .map(|m| m + 1)
            .unwrap_or(0);
        for &(u, v) in c_edges {
            let (a, b) = (u + offset, v + offset);
            all_edges.push(if a < b { (a, b) } else { (b, a) });
        }
        offset += kc;
    }
    all_edges.sort_unstable();
    (CanonGraph::from_sorted_edges(&all_edges), total_aut)
}

// ---------------------------------------------------------------------------
// UnorderedPair variable encoding (matches TupleVarSchema::UnorderedPair)
// ---------------------------------------------------------------------------

/// 0-indexed bit position for edge (a, b) with 1 ≤ a < b ≤ n.
/// Matches `TupleVarSchema::var_of_tuple([a, b]) − 1`.
#[inline]
pub(crate) fn edge_to_bit(a: u32, b: u32, n: u32) -> u32 {
    debug_assert!(a >= 1 && b <= n && a < b, "edge ({},{}) invalid for n={}", a, b, n);
    let mut idx = 0u32;
    for i in 1..a {
        idx += n - i;
    }
    idx + (b - a - 1)
}

/// Decode a 0-indexed bit position to the edge (a, b) with 1 ≤ a < b ≤ n.
#[inline]
pub(crate) fn bit_to_edge(mut bit: u32, n: u32) -> (u32, u32) {
    for a in 1..n {
        let width = n - a;
        if bit < width {
            return (a, a + 1 + bit);
        }
        bit -= width;
    }
    panic!("bit {} out of range for n={}", bit, n);
}

// ---------------------------------------------------------------------------
// MonoBits ↔ edge list for UnorderedPair schemas
// ---------------------------------------------------------------------------

use super::orbit_ns::MonoBits;

/// Decode a MonoBits for K_n (UnorderedPair schema) to a sorted edge list
/// with vertices 0-indexed as `a−1` and `b−1` (0..n−1).
pub(crate) fn monobits_to_edges(mut bits: MonoBits, n: u32) -> Vec<(u8, u8)> {
    let mut edges = Vec::new();
    while !bits.is_zero() {
        let bit = bits.trailing_zeros();
        let (a, b) = bit_to_edge(bit, n);
        // Convert to 0-indexed
        edges.push((a as u8 - 1, b as u8 - 1));
        bits.clear_lowest();
    }
    edges.sort_unstable();
    edges
}

/// Encode a canonical graph (vertices 0..k−1) back to MonoBits in K_n,
/// using the SMALLEST vertex labels {1..k} in K_n (= bits for edges {0,1}, {0,2}, …).
pub(crate) fn canon_to_monobits(g: &CanonGraph, n: u32) -> MonoBits {
    let mut bits = MonoBits::ZERO;
    for (u, v) in g.edge_iter() {
        // canonical vertices are 0-indexed; K_n uses 1-indexed → add 1
        bits.set_bit(edge_to_bit(u as u32 + 1, v as u32 + 1, n));
    }
    bits
}

/// Canonical form of a MonoBits for K_n.
pub(crate) fn canon_monobits(bits: MonoBits, n: u32) -> (CanonGraph, u64) {
    let edges = monobits_to_edges(bits, n);
    canonicalize(&edges)
}

// ---------------------------------------------------------------------------
// Orbit-size formula
// ---------------------------------------------------------------------------

/// Orbit size of a canonical graph G embedded in K_n under S_n.
/// = P(n, k) / |Aut(G)| where P(n,k) = n × (n−1) × … × (n−k+1).
pub(crate) fn orbit_size(g: &CanonGraph, aut: u64, n: u32) -> u64 {
    let k = g.n_verts as u32;
    if k > n {
        return 0;
    }
    let falling: u64 = ((n - k + 1)..=n).map(|x| x as u64).product();
    falling / aut
}

/// Pair orbit size for a combined edge set H = axiom_bits | mono_bits.
/// = P(n, k_H) / |Aut(H)|.
pub(crate) fn pair_orbit_size(axiom_bits: MonoBits, mono_bits: MonoBits, n: u32) -> u64 {
    let combined = axiom_bits | mono_bits;
    let edges = monobits_to_edges(combined, n);
    let (g, aut) = canonicalize(&edges);
    orbit_size(&g, aut, n)
}

// ---------------------------------------------------------------------------
// Orbit representative enumeration
// ---------------------------------------------------------------------------

/// Enumerate all orbit representatives for degree-≤d edge sets in K_n under S_n.
///
/// Returns a list of `(MonoBits_rep, CanonGraph, orbit_size)` sorted by degree
/// then canonical form. The MonoBits uses vertex labels {1..k} (the smallest
/// possible embedding in K_n).
///
/// Builds all canonical graphs incrementally: start from the empty graph, add
/// one edge at a time, keeping only canonical forms (lex-minimum isomorph).
pub(crate) fn enumerate_orbit_reps(n: u32, d: u32) -> Vec<(MonoBits, CanonGraph, u64)> {
    use std::collections::HashSet;

    let max_verts = (2 * d).min(n); // max active vertices for d edges

    // We work with abstract CanonGraphs (n-independent), then embed at the end.
    let mut seen: HashSet<CanonGraph> = HashSet::new();
    let mut reps_by_deg: Vec<Vec<CanonGraph>> = vec![Vec::new(); d as usize + 1];

    // Degree 0: empty graph
    let empty = CanonGraph::empty();
    seen.insert(empty.clone());
    reps_by_deg[0].push(empty);

    for k in 1..=(d as usize) {
        // For each canonical (k−1)-edge graph, try adding one more edge
        let prev = reps_by_deg[k - 1].clone();
        for g_prev in &prev {
            let kv = g_prev.n_verts as usize;

            // Try adding an edge (u, v) with u < v:
            // Case 1: both u, v ∈ existing vertices → v < kv, but (u,v) not in G
            // Case 2: v = kv (one new vertex) and u < kv, if kv < max_verts
            // Case 3: both new vertices (u=kv, v=kv+1), if kv+2 ≤ max_verts

            let existing_edges: std::collections::HashSet<(u8, u8)> =
                g_prev.edge_iter().collect();

            let max_v_new = if kv < max_verts as usize {
                kv as u8 + 1
            } else {
                kv as u8 - 1 // can't add new vertex, just intra-existing
            };

            for v in 1..=max_v_new {
                // u ranges 0..v; canonicalize() heals any vertex-numbering gaps.
                // Covers: both-existing (u<v<kv), one-new (v=kv, u<kv), both-new (v=kv+1, u=kv).
                for u in 0..v {
                    // Skip if edge already present
                    if existing_edges.contains(&(u, v)) {
                        continue;
                    }
                    // Skip if this would create vertices beyond max_verts
                    let new_kv = if v as usize >= kv { v as usize + 1 } else { kv };
                    if new_kv > max_verts as usize {
                        continue;
                    }

                    // Build new edge list
                    let mut new_edges: Vec<(u8, u8)> = g_prev.edge_iter().collect();
                    new_edges.push((u, v));

                    let (canon, _aut) = canonicalize(&new_edges);
                    if seen.insert(canon.clone()) {
                        reps_by_deg[k].push(canon);
                    }
                }
            }
        }
    }

    // Collect results with orbit sizes
    let mut result = Vec::new();
    for deg_reps in &reps_by_deg {
        for g in deg_reps {
            let edges: Vec<(u8, u8)> = g.edge_iter().collect();
            let (_, aut) = if edges.is_empty() {
                (CanonGraph::empty(), 1u64)
            } else {
                canonicalize(&edges)
            };
            let sz = orbit_size(g, aut, n);
            if sz == 0 {
                continue; // Can't embed (k > n); skip
            }
            let bits = canon_to_monobits(g, n);
            result.push((bits, g.clone(), sz));
        }
    }

    result
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn canon_empty() {
        let (g, aut) = canonicalize(&[]);
        assert_eq!(g, CanonGraph::empty());
        assert_eq!(aut, 1);
    }

    #[test]
    fn canon_single_edge() {
        let (g, aut) = canonicalize(&[(0u8, 1u8)]);
        let expected_edges: Vec<(u8, u8)> = g.edge_iter().collect();
        assert_eq!(expected_edges, vec![(0, 1)]);
        assert_eq!(g.n_verts, 2);
        assert_eq!(aut, 2); // K_2 has aut group of size 2
    }

    #[test]
    fn canon_triangle() {
        let (g, aut) = canonicalize(&[(0u8, 1u8), (0, 2), (1, 2)]);
        let edges: Vec<(u8, u8)> = g.edge_iter().collect();
        assert_eq!(edges, vec![(0, 1), (0, 2), (1, 2)]);
        assert_eq!(g.n_verts, 3);
        assert_eq!(aut, 6); // K_3 has aut = S_3 = 6
    }

    #[test]
    fn canon_two_edges_path_vs_matching() {
        // Path P3: 0-1-2
        let (gp, _) = canonicalize(&[(0u8, 1u8), (1, 2)]);
        // Matching K2+K2: 0-1, 2-3
        let (gm, _) = canonicalize(&[(0u8, 1u8), (2, 3)]);
        // These must be distinct canonical graphs
        assert_ne!(gp, gm);
    }

    #[test]
    fn canon_isomorphic_paths() {
        // Two different 0-indexed paths: (0,1),(0,2) vs (0,2),(1,2)
        let (g1, _) = canonicalize(&[(0u8, 1u8), (0, 2)]);
        let (g2, _) = canonicalize(&[(0u8, 2u8), (1, 2)]);
        assert_eq!(g1, g2, "isomorphic P3 paths must have same canon");
    }

    #[test]
    fn orbit_size_single_edge_k6() {
        let n = 6u32;
        let (g, aut) = canonicalize(&[(0u8, 1u8)]);
        let sz = orbit_size(&g, aut, n);
        // One edge in K_6: C(6,2) = 15 embeddings
        assert_eq!(sz, 15, "single edge in K_6 has 15 orbit members");
    }

    #[test]
    fn orbit_size_triangle_k6() {
        let n = 6u32;
        let (g, aut) = canonicalize(&[(0u8, 1u8), (0, 2), (1, 2)]);
        let sz = orbit_size(&g, aut, n);
        // K_3 in K_6: C(6,3) = 20 embeddings
        assert_eq!(sz, 20, "triangle in K_6 has 20 orbit members");
    }

    #[test]
    fn orbit_size_sum_equals_n_monos() {
        // For K_6 at degree d=2: total monomials of degree exactly 2 = C(15, 2) = 105
        // Sum of orbit sizes over all degree-2 orbit reps must equal 105
        let n = 6u32;
        let reps = enumerate_orbit_reps(n, 2);
        let sum: u64 = reps
            .iter()
            .filter(|(_, g, _)| g.n_edges == 2)
            .map(|(_, _, sz)| *sz)
            .sum();
        // C(15, 2) = 105
        assert_eq!(sum, 105, "sum of degree-2 orbit sizes must be C(15,2)=105");
    }

    #[test]
    fn orbit_size_sum_degree_all_k6() {
        // For K_6 at degree ≤ 3: sum over all orbit reps (deg 0..3) must equal
        // C(15,0)+C(15,1)+C(15,2)+C(15,3) = 1+15+105+455 = 576
        let n = 6u32;
        let reps = enumerate_orbit_reps(n, 3);
        let sum: u64 = reps.iter().map(|(_, _, sz)| *sz).sum();
        assert_eq!(sum, 576);
    }

    #[test]
    fn orbit_count_k6_degree7() {
        // From empirical data: K_6 at d=7 has 78 orbit reps
        let n = 6u32;
        let reps = enumerate_orbit_reps(n, 7);
        assert_eq!(reps.len(), 78, "K_6 at d=7: expected 78 orbit reps");
    }

    #[test]
    fn orbit_count_k7_degree7() {
        // From empirical data: K_7 at d=7 has 146 orbit reps
        let n = 7u32;
        let reps = enumerate_orbit_reps(n, 7);
        assert_eq!(reps.len(), 146, "K_7 at d=7: expected 146 orbit reps");
    }

    #[test]
    fn orbit_sum_k7_degree7() {
        // Sum of all orbit sizes at degree ≤ 7 must equal C(21, ≤7)
        // C(21,0)+...+C(21,7) = 1+21+210+1330+5985+20349+54264+116280 = 198440
        let n = 7u32;
        let reps = enumerate_orbit_reps(n, 7);
        let sum: u64 = reps.iter().map(|(_, _, sz)| *sz).sum();
        assert_eq!(sum, 198440);
    }

    #[test]
    fn bit_to_edge_roundtrip() {
        let n = 10u32;
        for a in 1..n {
            for b in (a + 1)..=n {
                let bit = edge_to_bit(a, b, n);
                let (ra, rb) = bit_to_edge(bit, n);
                assert_eq!((ra, rb), (a, b), "roundtrip failed for ({},{}) n={}", a, b, n);
            }
        }
    }

    #[test]
    fn canon_to_monobits_roundtrip() {
        let n = 10u32;
        let reps = enumerate_orbit_reps(n, 4);
        for (bits, g, _) in &reps {
            // Re-canonicalize the MonoBits and check it matches the stored CanonGraph
            let (g2, _) = canon_monobits(*bits, n);
            assert_eq!(*g, g2, "canon roundtrip failed for {:?}", g);
        }
    }
}
