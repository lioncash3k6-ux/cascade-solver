//! Stage B — pair-orbit enumeration + matrix scatter for PHP in orbit basis.
//!
//! Takes Stage A's mono-orbit reps and computes the matrix column structure
//! of the NS cert system in orbit basis. Each matrix column corresponds to
//! one G-orbit of `(axiom_idx, mono_bits)` pairs under the diagonal action.
//!
//! # Pair-orbit structure for PHP
//!
//! For PHP_{P,H} under G = S_P × S_H, there are two axiom orbits:
//!
//! * `α_pigeon`: P pigeon-totality axioms. Rep: `a_0` = totality for pigeon
//!   0. Stab_G(a_0) = S_{P-1} × S_H (fixes pigeon 0; permutes others +
//!   permutes all holes).
//! * `α_hole`: H · C(P, 2) hole-AMO axioms. Rep: `x_{0,0} · x_{1,0}` (hole
//!   0, pigeon pair {0, 1}). Stab_G(a_0) = S_2 × S_{P-2} × S_{H-1} (swaps
//!   {0,1}, permutes pigeons 2..P-1, permutes holes 1..H-1).
//!
//! For each axiom orbit α and mono orbit μ, the number of pair orbits is
//! the number of Stab_G(a_0)-orbits on μ (double-coset count). This can
//! be > 1 when Stab_G(a_0) is a proper subgroup of G.
//!
//! # Enumeration
//!
//! For each (α, μ): BFS in raw mono_bits over μ, grouping elements by
//! `Stab(a_0)`-connectivity. Each Stab-connected component = one pair
//! orbit. Reps = (a_0, smallest-m-in-subcomponent).
//!
//! Visits |μ| mono_bits in total per μ. Summed over all μ and both axiom
//! orbits, this is O(2 × n_monos) mono-bit visits — comparable to the
//! existing engine's monomial BFS but with much tighter memory usage
//! (HashSet per μ instead of global n_monos × n_axioms bitset).

use super::ns_fp::PolyP;
use super::php_orbit_enum::{enumerate_php_orbit_reps, OrbitIndex, PhpMatrix};
use super::poly::Monomial;
use std::collections::{BTreeMap, BTreeSet};

/// An axiom orbit under S_P × S_H.
#[derive(Clone, Debug)]
pub struct AxiomOrbit {
    /// Name for diagnostics (`"pigeon"` or `"hole"`).
    pub name: &'static str,
    /// Which adjacent-transposition generators of S_P × S_H fix the rep.
    /// Indexed into `[pigeon gens (P-1 of them), hole gens (H-1 of them)]`.
    pub stab_gen_mask: Vec<bool>,
    /// Size of this axiom orbit (= |G| / |Stab_G(a_0)|).
    pub size: u32,
    /// Degree of the axiom polynomial (max term degree).
    pub axiom_degree: u32,
}

/// PHP's two axiom orbits and their Stab-generator masks.
pub fn php_axiom_orbits(p: u32, h: u32) -> Vec<AxiomOrbit> {
    // Generator ordering (matching TupleVarSchema FullProduct):
    // pigeon swaps (0,1), (1,2), ..., (P-2,P-1): indices 0..P-1 (P-1 gens)
    // hole swaps (0,1), (1,2), ..., (H-2,H-1): indices P-1..P+H-2 (H-1 gens)
    let n_pigeon_gens = p.saturating_sub(1);
    let n_hole_gens = h.saturating_sub(1);
    let n_gens = (n_pigeon_gens + n_hole_gens) as usize;

    // Pigeon totality at pigeon 0: stabilized by pigeon swaps NOT involving
    // position 0 (i.e., skip generator index 0 which swaps pigeons 0↔1),
    // and by all hole swaps.
    let mut stab_pigeon = vec![true; n_gens];
    if n_pigeon_gens > 0 {
        stab_pigeon[0] = false; // (0, 1) moves pigeon 0
    }

    // Hole AMO with hole 0 + pigeons {0, 1}: stabilized by
    //   - pigeon swap (0, 1) — swaps within {0, 1}
    //   - pigeon swaps (i, i+1) for i ≥ 2 — outside {0, 1}
    //   - hole swaps (j, j+1) for j ≥ 1 — don't move hole 0
    let mut stab_hole = vec![false; n_gens];
    if n_pigeon_gens > 0 {
        stab_hole[0] = true; // (0, 1)
        // (1, 2) moves pigeon 1 → bad
        for i in 2..n_pigeon_gens as usize {
            stab_hole[i] = true;
        }
    }
    if n_hole_gens > 0 {
        // hole (0, 1) moves hole 0 → bad
        for j in 1..n_hole_gens as usize {
            stab_hole[(n_pigeon_gens as usize) + j] = true;
        }
    }

    vec![
        AxiomOrbit {
            name: "pigeon",
            stab_gen_mask: stab_pigeon,
            size: p,
            axiom_degree: 1,
        },
        AxiomOrbit {
            name: "hole",
            stab_gen_mask: stab_hole,
            size: h * p * (p - 1) / 2,
            axiom_degree: 2,
        },
    ]
}

/// Apply an adjacent-transposition generator (by index) to a `PhpMatrix`.
/// Generators 0..P-1 are pigeon swaps, indices P-1..P+H-2 are hole swaps.
pub fn apply_gen(m: &PhpMatrix, gen_idx: usize, p: u32, h: u32) -> PhpMatrix {
    let n_pigeon_gens = p.saturating_sub(1) as usize;
    if gen_idx < n_pigeon_gens {
        // Pigeon swap i ↔ i+1.
        let i = gen_idx as u32;
        apply_row_swap(m, i)
    } else {
        // Hole swap j ↔ j+1.
        let j = (gen_idx - n_pigeon_gens) as u32;
        apply_col_swap(m, j)
    }
}

fn apply_row_swap(m: &PhpMatrix, i: u32) -> PhpMatrix {
    let h = m.h as u32;
    let mask = (1u128 << h) - 1;
    let a = (m.bits >> (i * h)) & mask;
    let b = (m.bits >> ((i + 1) * h)) & mask;
    let rest = m.bits & !((mask << (i * h)) | (mask << ((i + 1) * h)));
    PhpMatrix::from_bits(
        rest | (b << (i * h)) | (a << ((i + 1) * h)),
        m.p as u32,
        h,
    )
}

fn apply_col_swap(m: &PhpMatrix, j: u32) -> PhpMatrix {
    let h = m.h as u32;
    let mut out = 0u128;
    for i in 0..m.p as u32 {
        let row = m.row(i) as u128;
        let bj = (row >> j) & 1;
        let bj1 = (row >> (j + 1)) & 1;
        let new_row = (row & !((1u128 << j) | (1u128 << (j + 1))))
            | (bj1 << j)
            | (bj << (j + 1));
        out |= new_row << (i * h);
    }
    PhpMatrix::from_bits(out, m.p as u32, h)
}

/// Apply a generator to an axiom index, for axiom orbit α with rep a_0.
/// Given a_0 is pigeon totality at pigeon 0 OR hole AMO at hole 0 / pigeons
/// {0,1}, and axioms are labeled by a canonical tuple:
///   pigeon totality: labeled by pigeon index (0..P-1).
///   hole AMO: labeled by (hole_idx, pigeon_lo, pigeon_hi) with pigeon_lo <
///     pigeon_hi.
/// This function returns the new label after applying `gen_idx`.
pub fn apply_gen_to_axiom_pigeon(axiom_pigeon: u32, gen_idx: usize, p: u32) -> u32 {
    let n_pigeon_gens = p.saturating_sub(1) as usize;
    if gen_idx < n_pigeon_gens {
        let swap_lo = gen_idx as u32;
        if axiom_pigeon == swap_lo {
            swap_lo + 1
        } else if axiom_pigeon == swap_lo + 1 {
            swap_lo
        } else {
            axiom_pigeon
        }
    } else {
        // Hole gen doesn't affect pigeon label.
        axiom_pigeon
    }
}

/// Hole AMO axioms are labeled by (hole, {p_lo, p_hi}) with p_lo < p_hi.
/// Returns new label after applying `gen_idx`.
pub fn apply_gen_to_axiom_hole(
    axiom: (u32, u32, u32),
    gen_idx: usize,
    p: u32,
    _h: u32,
) -> (u32, u32, u32) {
    let n_pigeon_gens = p.saturating_sub(1) as usize;
    let (hole, lo, hi) = axiom;
    if gen_idx < n_pigeon_gens {
        // Pigeon swap k ↔ k+1. Permute {lo, hi} accordingly.
        let k = gen_idx as u32;
        let swap = |x: u32| -> u32 {
            if x == k {
                k + 1
            } else if x == k + 1 {
                k
            } else {
                x
            }
        };
        let new_lo_raw = swap(lo);
        let new_hi_raw = swap(hi);
        let (a, b) = if new_lo_raw < new_hi_raw {
            (new_lo_raw, new_hi_raw)
        } else {
            (new_hi_raw, new_lo_raw)
        };
        (hole, a, b)
    } else {
        // Hole swap j ↔ j+1.
        let j = (gen_idx - n_pigeon_gens) as u32;
        let new_hole = if hole == j {
            j + 1
        } else if hole == j + 1 {
            j
        } else {
            hole
        };
        (new_hole, lo, hi)
    }
}

/// A single pair orbit: rep + orbit size.
#[derive(Clone, Debug)]
pub struct PairOrbit {
    /// Which axiom orbit (index into `php_axiom_orbits` result: 0 = pigeon,
    /// 1 = hole).
    pub axiom_orbit: u32,
    /// Mono orbit index (into Stage A's reps).
    pub mono_orbit: u32,
    /// Monomial representative within the Stab(a_0)-sub-orbit. This is a
    /// specific member of mono_orbit; by convention we pick the lex-min
    /// m_bits within the sub-orbit.
    pub mono_rep_bits: u128,
    /// |pair orbit| = |α| · sub_orbit_size. Needed for closed-form scatter:
    /// c_κ = |pair orbit| / |orbit κ| · A(κ) mod p.
    pub size: u64,
}

fn uf_find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

fn uf_union(parent: &mut [usize], a: usize, b: usize) {
    let ra = uf_find(parent, a);
    let rb = uf_find(parent, b);
    if ra != rb {
        parent[ra] = rb;
    }
}

/// Enumerate all pair orbits for PHP_{P,H} mono orbits from Stage A, up
/// to total degree `d` (axiom_degree + mono_degree ≤ d).
///
/// For each axiom orbit α and mono orbit μ with `deg(a_0) + deg(m_0) ≤ d`:
///   1. Enumerate all of μ in raw `m_bits` space by BFS under ALL G
///      generators, starting from `μ`'s Stage A rep.
///   2. Build a union-find over μ's elements where edges come ONLY from
///      Stab_G(a_0) generators. Each UF component = one Stab-sub-orbit =
///      one pair orbit.
///   3. Pick the lex-min mono as sub-orbit rep.
pub fn enumerate_php_pair_orbits(
    p: u32,
    h: u32,
    d: u32,
    mono_orbits: &[PhpMatrix],
) -> (Vec<PairOrbit>, Vec<u64>) {
    let axiom_orbits = php_axiom_orbits(p, h);
    let n_gens = (p.saturating_sub(1) + h.saturating_sub(1)) as usize;

    let mut pair_orbits: Vec<PairOrbit> = Vec::new();
    let mut mu_sizes: Vec<u64> = Vec::with_capacity(mono_orbits.len());

    use std::collections::HashMap;
    // Reuse allocations across μ iterations.
    let mut idx_of_m: HashMap<u128, u32> = HashMap::new();
    let mut mu_members: Vec<u128> = Vec::new();
    let mut queue: Vec<u128> = Vec::new();

    for (mu_idx, m0) in mono_orbits.iter().enumerate() {
        let mu_degree = m0.popcount();
        // Step 1: enumerate all of μ via FULL G-BFS from m0.
        idx_of_m.clear();
        mu_members.clear();
        queue.clear();
        idx_of_m.insert(m0.bits, 0);
        mu_members.push(m0.bits);
        queue.push(m0.bits);
        while let Some(mb) = queue.pop() {
            let m = PhpMatrix::from_bits(mb, p, h);
            for gi in 0..n_gens {
                let img = apply_gen(&m, gi, p, h);
                if let std::collections::hash_map::Entry::Vacant(v) =
                    idx_of_m.entry(img.bits)
                {
                    let new_idx = mu_members.len() as u32;
                    v.insert(new_idx);
                    mu_members.push(img.bits);
                    queue.push(img.bits);
                }
            }
        }
        mu_sizes.push(mu_members.len() as u64);

        // Step 2: for each axiom orbit α, build UF over μ with edges from
        // Stab(a_0) generators only.
        for (a_idx, axiom) in axiom_orbits.iter().enumerate() {
            // Degree budget: only include (α, μ) pairs with
            // axiom.degree + μ.degree ≤ d, matching the existing engine.
            if axiom.axiom_degree + mu_degree > d {
                continue;
            }
            let stab_mask = &axiom.stab_gen_mask;
            let n = mu_members.len();
            let mut parent: Vec<usize> = (0..n).collect();
            for (i, &mb) in mu_members.iter().enumerate() {
                let m = PhpMatrix::from_bits(mb, p, h);
                for gi in 0..n_gens {
                    if !stab_mask[gi] {
                        continue;
                    }
                    let img = apply_gen(&m, gi, p, h);
                    let j = idx_of_m[&img.bits] as usize;
                    uf_union(&mut parent, i, j);
                }
            }
            // Step 3: pick one rep per UF component.
            let mut root_to_min: BTreeMap<usize, u128> = BTreeMap::new();
            for i in 0..n {
                let root = uf_find(&mut parent, i);
                let mb = mu_members[i];
                root_to_min
                    .entry(root)
                    .and_modify(|m| {
                        if mb < *m {
                            *m = mb;
                        }
                    })
                    .or_insert(mb);
            }
            // Also collect the size of each sub-orbit — needed by
            // closed-form scatter.
            let mut root_size: BTreeMap<usize, u64> = BTreeMap::new();
            for i in 0..n {
                let root = uf_find(&mut parent, i);
                *root_size.entry(root).or_insert(0) += 1;
            }
            for (root, rep_bits) in root_to_min {
                let sub_size = root_size[&root];
                pair_orbits.push(PairOrbit {
                    axiom_orbit: a_idx as u32,
                    mono_orbit: mu_idx as u32,
                    mono_rep_bits: rep_bits,
                    size: (axiom.size as u64) * sub_size,
                });
            }
        }
    }

    (pair_orbits, mu_sizes)
}

/// Polynomial term list for a single PHP axiom identified by label.
/// Each entry is `(support_bits, coef)` — the term's variable support
/// encoded as a `PhpMatrix`-compatible bitset, and its 𝔽_p coefficient.
pub fn axiom_terms(
    axiom_orbit_idx: u32,
    pigeon_label: u32,
    hole_label: (u32, u32, u32),
    p: u32,
    h: u32,
    prime: u8,
) -> Vec<(u128, u8)> {
    if axiom_orbit_idx == 0 {
        // Pigeon totality at pigeon `pigeon_label`:
        // x_{p, 0} + x_{p, 1} + ... + x_{p, H-1} - 1 = 0
        // Terms: H single-cell + constant -1 mod prime.
        let mut out = Vec::with_capacity(h as usize + 1);
        for j in 0..h {
            let bit = 1u128 << (pigeon_label * h + j);
            out.push((bit, 1u8));
        }
        out.push((0u128, (prime - 1))); // constant term
        out
    } else {
        // Hole AMO: x_{p_lo, hole} · x_{p_hi, hole}. Single term.
        let (hole, p_lo, p_hi) = hole_label;
        let bits = (1u128 << (p_lo * h + hole)) | (1u128 << (p_hi * h + hole));
        vec![(bits, 1u8)]
    }
}

/// A pair-orbit member: (axiom label, mono bits). Axiom label depends on
/// which axiom orbit the pair belongs to.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum AxiomLabel {
    Pigeon(u32),               // pigeon index 0..P-1
    Hole(u32, u32, u32),       // (hole, p_lo, p_hi) with p_lo < p_hi
}

/// Apply a G generator (by index) to an axiom label.
fn apply_gen_to_axiom(label: AxiomLabel, gen_idx: usize, p: u32, h: u32) -> AxiomLabel {
    match label {
        AxiomLabel::Pigeon(pig) => {
            AxiomLabel::Pigeon(apply_gen_to_axiom_pigeon(pig, gen_idx, p))
        }
        AxiomLabel::Hole(hole, lo, hi) => {
            let (nhole, nlo, nhi) =
                apply_gen_to_axiom_hole((hole, lo, hi), gen_idx, p, h);
            AxiomLabel::Hole(nhole, nlo, nhi)
        }
    }
}

/// Extract the bits representation of an axiom label's terms. Wrapper
/// around `axiom_terms` that picks the right label type.
fn axiom_terms_of_label(
    axiom_orbit_idx: u32,
    label: AxiomLabel,
    p: u32,
    h: u32,
    prime: u8,
) -> Vec<(u128, u8)> {
    match label {
        AxiomLabel::Pigeon(pig) => axiom_terms(axiom_orbit_idx, pig, (0, 0, 0), p, h, prime),
        AxiomLabel::Hole(hole, lo, hi) => {
            axiom_terms(axiom_orbit_idx, 0, (hole, lo, hi), p, h, prime)
        }
    }
}

/// Color-refinement-based Stab(pair)-orbit computation for holes, given a
/// pair orbit with axiom_orbit=0 (pigeon totality at pigeon 0) and monomial
/// rep m*.
///
/// Returns `hole_orbit_id[j]` such that two holes j, j' are in the same
/// Stab(pair)-orbit iff `hole_orbit_id[j] == hole_orbit_id[j']`.
///
/// Algorithm: iterated color refinement on the bipartite graph of m* with
/// pigeon 0 distinguished. Initialize colors by local structure, refine by
/// multisets of neighbor colors until stable. For sparse m* (d ≤ 7 cells on
/// up to 8×7 grid), refinement converges to the true Aut-orbit partition.
fn hole_orbits_under_pigeon_stab(m_bits: u128, p: u32, h: u32) -> Vec<u32> {
    let p_usize = p as usize;
    let h_usize = h as usize;
    // Adjacency: m_bits cell (i, j) at bit i*h + j.
    let cell = |i: u32, j: u32| -> bool {
        let pos = i * h + j;
        (m_bits >> pos) & 1 == 1
    };

    // Initial hole colors: (has pigeon 0 connection, # non-0 pigeons connected).
    let mut hole_color: Vec<u64> = (0..h)
        .map(|j| {
            let has_p0 = if cell(0, j) { 1u64 } else { 0 };
            let non_0_count: u64 =
                (1..p).filter(|&i| cell(i, j)).count() as u64;
            (has_p0 << 32) | non_0_count
        })
        .collect();
    // Initial pigeon colors: (is pigeon 0, # holes connected).
    // Pigeon 0 gets a unique color (distinguishes pigeon 0).
    let mut pigeon_color: Vec<u64> = (0..p)
        .map(|i| {
            let is_p0 = if i == 0 { u64::MAX } else { 0 };
            let pop: u64 = (0..h).filter(|&j| cell(i, j)).count() as u64;
            is_p0 ^ pop
        })
        .collect();

    // Iterate color refinement until stable (max 8 iterations — plenty for
    // graphs of this size).
    for _iter in 0..8 {
        let mut new_hole_color: Vec<u64> = Vec::with_capacity(h_usize);
        for j in 0..h {
            let mut neighbor_pigeon_colors: Vec<u64> =
                (0..p).filter(|&i| cell(i, j)).map(|i| pigeon_color[i as usize]).collect();
            neighbor_pigeon_colors.sort();
            // Hash the multiset.
            let mut hash: u64 = hole_color[j as usize];
            for c in neighbor_pigeon_colors {
                hash = hash.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(c);
            }
            new_hole_color.push(hash);
        }
        let mut new_pigeon_color: Vec<u64> = Vec::with_capacity(p_usize);
        for i in 0..p {
            let mut neighbor_hole_colors: Vec<u64> =
                (0..h).filter(|&j| cell(i, j)).map(|j| hole_color[j as usize]).collect();
            neighbor_hole_colors.sort();
            let mut hash: u64 = pigeon_color[i as usize];
            for c in neighbor_hole_colors {
                hash = hash.wrapping_mul(0x9E3779B97F4A7C15).wrapping_add(c);
            }
            new_pigeon_color.push(hash);
        }
        if new_hole_color == hole_color && new_pigeon_color == pigeon_color {
            break;
        }
        hole_color = new_hole_color;
        pigeon_color = new_pigeon_color;
    }

    // Compact colors to contiguous ids.
    let mut sorted_colors: Vec<u64> = hole_color.iter().copied().collect();
    sorted_colors.sort();
    sorted_colors.dedup();
    hole_color
        .iter()
        .map(|c| sorted_colors.binary_search(c).unwrap() as u32)
        .collect()
}

/// Build the orbit-basis NS matrix via BFS over pair-orbit members.
/// Slow (O(Σ |pair orbit|)) but matches existing-engine semantics exactly.
/// Use for validating the closed-form scatter.
pub fn build_orbit_matrix_bfs(
    p: u32,
    h: u32,
    d: u32,
    prime: u8,
    mono_orbits: &[PhpMatrix],
    pair_orbits: &[PairOrbit],
) -> Vec<Vec<u8>> {
    let orbit_index = OrbitIndex::new(mono_orbits);
    let n_rows = mono_orbits.len();
    let n_cols = pair_orbits.len();
    let n_gens = (p.saturating_sub(1) + h.saturating_sub(1)) as usize;

    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    for (col, po) in pair_orbits.iter().enumerate() {
        let seed_label = if po.axiom_orbit == 0 {
            AxiomLabel::Pigeon(0)
        } else {
            AxiomLabel::Hole(0, 0, 1)
        };
        use std::collections::HashSet;
        let mut visited: HashSet<(AxiomLabel, u128)> = HashSet::new();
        let mut queue: Vec<(AxiomLabel, u128)> = Vec::new();
        visited.insert((seed_label, po.mono_rep_bits));
        queue.push((seed_label, po.mono_rep_bits));
        while let Some((alabel, mb)) = queue.pop() {
            let terms = axiom_terms_of_label(po.axiom_orbit, alabel, p, h, prime);
            for (term_bits, coef) in &terms {
                let product = term_bits | mb;
                if (product.count_ones() as u32) > d {
                    continue;
                }
                let pm = PhpMatrix::from_bits(product, p, h);
                let kappa = orbit_index.of(pm);
                if mono_orbits[kappa].bits == product {
                    matrix[kappa][col] =
                        ((matrix[kappa][col] as u16 + *coef as u16) % prime as u16) as u8;
                }
            }
            let m = PhpMatrix::from_bits(mb, p, h);
            for gi in 0..n_gens {
                let img = apply_gen(&m, gi, p, h);
                let new_label = apply_gen_to_axiom(alabel, gi, p, h);
                let state = (new_label, img.bits);
                if visited.insert(state) {
                    queue.push(state);
                }
            }
        }
    }
    let empty_m = PhpMatrix::from_bits(0, p, h);
    let one_row = orbit_index.of(empty_m);
    matrix[one_row][n_cols] = 1;
    matrix
}

/// Compare closed-form scatter to BFS scatter for a given PHP problem.
/// Returns count of cells where they disagree and the first disagreeing
/// (row, col, closed_form_val, bfs_val).
pub fn compare_scatter_methods(
    p: u32,
    h: u32,
    d: u32,
    prime: u8,
) -> (usize, Option<(usize, usize, u8, u8)>) {
    let mono_orbits = enumerate_php_orbit_reps(p, h, d);
    let (pair_orbits, mu_sizes) = enumerate_php_pair_orbits(p, h, d, &mono_orbits);
    let m_closed =
        build_orbit_matrix(p, h, d, prime, &mono_orbits, &pair_orbits, &mu_sizes);
    let m_bfs = build_orbit_matrix_bfs(p, h, d, prime, &mono_orbits, &pair_orbits);
    let mut disagreements = 0;
    let mut first_disagree: Option<(usize, usize, u8, u8)> = None;
    for r in 0..m_closed.len() {
        for c in 0..m_closed[0].len() {
            if m_closed[r][c] != m_bfs[r][c] {
                disagreements += 1;
                if first_disagree.is_none() {
                    first_disagree = Some((r, c, m_closed[r][c], m_bfs[r][c]));
                }
            }
        }
    }
    (disagreements, first_disagree)
}

/// Build the orbit-basis NS matrix for PHP_{P,H} at degree d over 𝔽_`prime`.
///
/// Rows: mono orbits from Stage A.
/// Cols: pair orbits from Stage B.2 (+1 RHS column at end).
///
/// # Correct closed-form scatter
///
/// `matrix[κ][col] = (|pair orbit| · A'(κ)) · inv(|orbit κ|) mod p`
///
/// where the **weighted** term-sum accounts for Stab(pair)-orbit sizes:
///
/// `A'(κ) = Σ_{Stab(pair)-orbits [t] of terms(a_0) with orbit(t_rep ∪ m*) = κ} |[t]| · coef(rep [t])`
///
/// For pigeon axiom `a_0` = totality at pigeon 0: Stab(pair) permutes the
/// H holes according to Aut(m* with pigeon 0 marked). For term `t_0 =
/// x_{0,j}`, `|[t]|` = |Stab(pair)-orbit of hole j|, computed by color
/// refinement on the bipartite graph m*.
///
/// For hole AMO axiom: single term, Stab(pair) fixes it, `|[t]| = 1`.
///
/// ## History
///
/// A buggier prior version had `|[t]| = 1` uniformly — correct only when
/// `Stab(pair) ⊆ Stab(t_0 ∪ m*)` for each term, which holds for hole AMO
/// (always) and pigeon terms where `(0, j) ∈ m*`. For pigeon terms where
/// `(0, j) ∉ m*` the factor can be > 1; the buggy formula over-split this
/// contribution into too many terms. This showed up as rank deficiency at
/// PHP_{8,7} d=7 (smaller cases lucked out).
///
/// Cost: O(n_pair_orbits · (terms_per_axiom_rep + color_refinement)). Per
/// pair orbit we iterate H+1 pigeon terms or 1 hole term, plus O(P·H) for
/// color refinement on the m* graph. No pair-orbit BFS.
pub fn build_orbit_matrix(
    p: u32,
    h: u32,
    d: u32,
    prime: u8,
    mono_orbits: &[PhpMatrix],
    pair_orbits: &[PairOrbit],
    mu_sizes: &[u64],
) -> Vec<Vec<u8>> {
    let orbit_index = OrbitIndex::new(mono_orbits);
    let n_rows = mono_orbits.len();
    let n_cols = pair_orbits.len();

    let mut matrix: Vec<Vec<u8>> = vec![vec![0u8; n_cols + 1]; n_rows];

    // Cache: inv(|orbit κ| mod p) per κ.
    let inv_mu: Vec<u8> = mu_sizes
        .iter()
        .map(|&s| {
            let s_mod = (s % prime as u64) as u8;
            assert!(s_mod != 0, "prime {} divides |orbit| ({})", prime, s);
            mod_inv(s_mod, prime)
        })
        .collect();

    for (col, po) in pair_orbits.iter().enumerate() {
        let pair_size_mod = (po.size % prime as u64) as u8;

        // A'(κ) aggregator, indexed by mono-orbit id κ.
        let mut a_of_kappa: BTreeMap<usize, u16> = BTreeMap::new();

        if po.axiom_orbit == 0 {
            // Pigeon axiom: terms are x_{0, j} for j=0..H-1 (coef 1 each) +
            // constant (coef prime-1). Stab(pair)-orbit size of term
            // x_{0, j} = |hole_orbits_under_pigeon_stab(m*)[j]|'s class size.
            // Constant term: Stab(pair)-orbit size 1 always.
            let hole_orbits = hole_orbits_under_pigeon_stab(po.mono_rep_bits, p, h);
            // Compute class size per hole.
            let mut class_size: Vec<u32> = vec![0; h as usize];
            for &c in &hole_orbits {
                class_size[c as usize] += 1;
            }
            // Group contributions: for each Stab(pair)-orbit of holes,
            // contribute orbit_size × 1 to the κ of (x_{0, rep} ∪ m*).
            // Skip duplicates within an orbit (pick one rep hole per orbit).
            let mut orbit_seen: Vec<bool> = vec![false; h as usize];
            for j in 0..h {
                let c = hole_orbits[j as usize] as usize;
                if orbit_seen[c] {
                    continue;
                }
                orbit_seen[c] = true;
                let orbit_sz = class_size[c];
                let term_bit: u128 = 1u128 << (0 * h + j); // x_{0, j} bit
                let product = term_bit | po.mono_rep_bits;
                if (product.count_ones() as u32) > d {
                    continue;
                }
                let pm = PhpMatrix::from_bits(product, p, h);
                let kappa = orbit_index.of(pm);
                let slot = a_of_kappa.entry(kappa).or_insert(0u16);
                *slot = (*slot + (orbit_sz as u16 * 1u16) % prime as u16) % prime as u16;
            }
            // Constant term.
            let kappa_const = orbit_index.of(PhpMatrix::from_bits(po.mono_rep_bits, p, h));
            let slot = a_of_kappa.entry(kappa_const).or_insert(0u16);
            *slot = (*slot + (prime - 1) as u16) % prime as u16;
        } else {
            // Hole AMO axiom: one term = x_{p_lo, hole} · x_{p_hi, hole}
            // with coef 1. Stab(pair)-orbit size = 1 (term is Stab-fixed).
            let term_bits = (1u128 << 0) | (1u128 << h); // (0, 0) and (1, 0)
            let product = term_bits | po.mono_rep_bits;
            if (product.count_ones() as u32) <= d {
                let pm = PhpMatrix::from_bits(product, p, h);
                let kappa = orbit_index.of(pm);
                let slot = a_of_kappa.entry(kappa).or_insert(0u16);
                *slot = (*slot + 1) % prime as u16;
            }
        }

        // matrix[κ][col] = pair_size · A'(κ) · inv(|orbit κ|) mod p.
        for (kappa, a_val) in a_of_kappa {
            let v = (pair_size_mod as u16 * a_val) % prime as u16;
            let v = (v * inv_mu[kappa] as u16) % prime as u16;
            matrix[kappa][col] = v as u8;
        }
    }

    // RHS column: target "constant 1" — row for empty orbit gets 1.
    let empty_m = PhpMatrix::from_bits(0, p, h);
    let one_row = orbit_index.of(empty_m);
    matrix[one_row][n_cols] = 1;

    matrix
}

/// Mod-p inverse for small `prime`. `assert!(a != 0 && a < prime)`.
fn mod_inv(a: u8, prime: u8) -> u8 {
    for k in 1..prime {
        if (a as u16 * k as u16) % prime as u16 == 1 {
            return k;
        }
    }
    panic!("no inverse of {} mod {}", a, prime);
}

/// Gaussian elimination over 𝔽_p on augmented matrix `[A | b]`. Mutates
/// `matrix`. Returns `Some(solution_vector)` of length `n_cols` iff
/// consistent, else `None`. `n_cols` is `matrix[0].len() - 1`.
fn gaussian_solve(matrix: &mut [Vec<u8>], prime: u8) -> Option<Vec<u8>> {
    let n_rows = matrix.len();
    if n_rows == 0 {
        return Some(Vec::new());
    }
    let n_cols = matrix[0].len() - 1;
    let mut pivot_row_of_col: Vec<Option<usize>> = vec![None; n_cols];
    let mut row = 0usize;
    for col in 0..n_cols {
        let mut pivot: Option<usize> = None;
        for r in row..n_rows {
            if matrix[r][col] != 0 {
                pivot = Some(r);
                break;
            }
        }
        let pivot = match pivot {
            Some(p) => p,
            None => continue,
        };
        matrix.swap(pivot, row);
        let a = matrix[row][col];
        if a != 1 {
            let inv = mod_inv(a, prime);
            for v in &mut matrix[row] {
                *v = ((*v as u16 * inv as u16) % prime as u16) as u8;
            }
        }
        pivot_row_of_col[col] = Some(row);
        for r in 0..n_rows {
            if r == row {
                continue;
            }
            let k = matrix[r][col];
            if k == 0 {
                continue;
            }
            let neg_k = prime - k;
            for c in col..=n_cols {
                let prod = (neg_k as u16 * matrix[row][c] as u16) % prime as u16;
                matrix[r][c] = ((matrix[r][c] as u16 + prod) % prime as u16) as u8;
            }
        }
        row += 1;
    }
    // Consistency check: any all-zero LHS row with nonzero RHS ⇒ no solution.
    for r in 0..n_rows {
        if matrix[r][..n_cols].iter().all(|&v| v == 0) && matrix[r][n_cols] != 0 {
            if std::env::var("CASCADE_PHP_ORBIT_TIMING").is_ok() {
                eprintln!(
                    "[php-orbit] gaussian INCONSISTENT: row {} of {} has all-zero LHS but RHS = {} (pivots set: {})",
                    r,
                    n_rows,
                    matrix[r][n_cols],
                    pivot_row_of_col.iter().filter(|p| p.is_some()).count()
                );
            }
            return None;
        }
    }
    let mut solution = vec![0u8; n_cols];
    for (col, pr) in pivot_row_of_col.iter().enumerate() {
        if let Some(pivot_row) = pr {
            solution[col] = matrix[*pivot_row][n_cols];
        }
    }
    Some(solution)
}

/// Convert bits back to a `Monomial` (variables 1-indexed).
fn bits_to_mono(bits: u128) -> Monomial {
    let mut s = BTreeSet::new();
    let mut b = bits;
    while b != 0 {
        let lo = b.trailing_zeros();
        s.insert(lo + 1);
        b &= b - 1;
    }
    Monomial(s)
}

/// Map a raw axiom index (in the original `php_functional` order) from a
/// pair-orbit member's `AxiomLabel`. Pigeon indices 0..P-1 become raw axiom
/// idx 0..P-1. Hole axioms are indexed as
///   `P + (hole * C(P, 2)) + (triangular pair index of (p_lo, p_hi))`
/// matching the `php_functional` construction order:
///   hole outer loop, then p1 loop, then p2 > p1 loop.
fn raw_axiom_idx(label: AxiomLabel, p: u32, h: u32) -> usize {
    match label {
        AxiomLabel::Pigeon(pig) => pig as usize,
        AxiomLabel::Hole(hole, lo, hi) => {
            // php_functional uses 1-indexed p1, p2 with p1 < p2 in order:
            //   for h in 1..=H: for p1 in 1..=P: for p2 in p1+1..=P
            // We're 0-indexed internally; the (p1, p2) pairs in order are
            //   (1,2), (1,3), ..., (1,P), (2,3), ..., (P-1, P)
            // (p1=lo+1, p2=hi+1 in 1-indexed form).
            let amos_per_hole = (p * (p - 1) / 2) as usize;
            let base = p as usize + (hole as usize) * amos_per_hole;
            // Pair index: for (lo, hi) with lo < hi (0-indexed), count
            //   Σ_{l < lo} (P - 1 - l) + (hi - lo - 1)
            let mut pair_idx: usize = 0;
            for l in 0..lo {
                pair_idx += (p - 1 - l) as usize;
            }
            pair_idx += (hi - lo - 1) as usize;
            base + pair_idx
        }
    }
    // Reference `h` to avoid unused-var warning (it's needed by callers).
}

/// Reconstruct the NS certificate from the Gaussian solution.
///
/// For each pair orbit with nonzero coefficient `λ`, walk its members via
/// G-BFS; for each member (a, m) in the orbit, accumulate `λ · m` into
/// the multiplier polynomial for raw axiom index `a`.
fn reconstruct_cert(
    p: u32,
    h: u32,
    prime: u8,
    pair_orbits: &[PairOrbit],
    solution: &[u8],
) -> BTreeMap<usize, PolyP> {
    let n_gens = (p.saturating_sub(1) + h.saturating_sub(1)) as usize;
    let mut mults: BTreeMap<usize, PolyP> = BTreeMap::new();
    for (col, &coef) in solution.iter().enumerate() {
        if coef == 0 {
            continue;
        }
        let po = &pair_orbits[col];
        let seed_label = if po.axiom_orbit == 0 {
            AxiomLabel::Pigeon(0)
        } else {
            AxiomLabel::Hole(0, 0, 1)
        };
        use std::collections::HashSet;
        let mut visited: HashSet<(AxiomLabel, u128)> = HashSet::new();
        let mut queue: Vec<(AxiomLabel, u128)> = Vec::new();
        visited.insert((seed_label, po.mono_rep_bits));
        queue.push((seed_label, po.mono_rep_bits));
        while let Some((alabel, mb)) = queue.pop() {
            let ax_idx = raw_axiom_idx(alabel, p, h);
            let mu_mono = bits_to_mono(mb);
            let entry = mults.entry(ax_idx).or_insert_with(|| PolyP::zero(prime));
            let term = PolyP::single(prime, mu_mono, coef);
            entry.add_assign(&term);
            let m = PhpMatrix::from_bits(mb, p, h);
            for gi in 0..n_gens {
                let img = apply_gen(&m, gi, p, h);
                let new_label = apply_gen_to_axiom(alabel, gi, p, h);
                let state = (new_label, img.bits);
                if visited.insert(state) {
                    queue.push(state);
                }
            }
        }
    }
    mults
}

/// Stage B+C end-to-end: find an NS cert for PHP_{P,H} at degree d over
/// 𝔽_`prime` using the orbit-basis pipeline. Returns `Some(mults)` —
/// multipliers keyed by raw axiom index — or `None` if no cert.
pub fn find_php_orbit_cert(
    p: u32,
    h: u32,
    d: u32,
    prime: u8,
) -> Option<BTreeMap<usize, PolyP>> {
    let verbose = std::env::var("CASCADE_PHP_ORBIT_TIMING").is_ok();
    let t0 = std::time::Instant::now();
    let mono_orbits = enumerate_php_orbit_reps(p, h, d);
    if verbose {
        eprintln!(
            "[php-orbit] stage A (mono orbits): {} in {:.3}s",
            mono_orbits.len(),
            t0.elapsed().as_secs_f64()
        );
    }
    let t = std::time::Instant::now();
    let (pair_orbits, mu_sizes) = enumerate_php_pair_orbits(p, h, d, &mono_orbits);
    if verbose {
        eprintln!(
            "[php-orbit] stage B.2 (pair orbits + μ BFS): {} pair orbits in {:.3}s",
            pair_orbits.len(),
            t.elapsed().as_secs_f64()
        );
    }
    let t = std::time::Instant::now();
    let mut matrix =
        build_orbit_matrix(p, h, d, prime, &mono_orbits, &pair_orbits, &mu_sizes);
    if verbose {
        eprintln!(
            "[php-orbit] stage B.3 (closed-form scatter): {:.3}s",
            t.elapsed().as_secs_f64()
        );
    }
    if verbose {
        let n_nonzero: usize = matrix.iter().map(|r| r[..pair_orbits.len()].iter().filter(|&&v| v != 0).count()).sum();
        let row_0_entries: usize = matrix[0][..pair_orbits.len()].iter().filter(|&&v| v != 0).count();
        let empty_rows: usize = matrix.iter().filter(|r| r[..pair_orbits.len()].iter().all(|&v| v == 0)).count();
        eprintln!(
            "[php-orbit] matrix stats: {} rows × {} cols, {} nonzero entries, row 0 has {} entries, {} all-zero-LHS rows",
            matrix.len(),
            pair_orbits.len(),
            n_nonzero,
            row_0_entries,
            empty_rows,
        );
    }
    let t = std::time::Instant::now();
    let solution = match gaussian_solve(&mut matrix, prime) {
        Some(s) => s,
        None => {
            if verbose {
                eprintln!(
                    "[php-orbit] stage C.1 (gaussian): {:.3}s — INCONSISTENT (no cert)",
                    t.elapsed().as_secs_f64()
                );
            }
            return None;
        }
    };
    if verbose {
        eprintln!(
            "[php-orbit] stage C.1 (gaussian): {:.3}s",
            t.elapsed().as_secs_f64()
        );
    }
    let t = std::time::Instant::now();
    let mults = reconstruct_cert(p, h, prime, &pair_orbits, &solution);
    if verbose {
        eprintln!(
            "[php-orbit] stage C.2 (cert reconstruction): {:.3}s ({} multipliers)",
            t.elapsed().as_secs_f64(),
            mults.len()
        );
    }
    Some(mults)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::algebra::php_orbit_enum::enumerate_php_orbit_reps;

    /// PHP_{3,2} d=2: existing engine reports 4 pair orbits.
    #[test]
    fn pair_orbit_count_php_3_2_d2() {
        let mono_orbits = enumerate_php_orbit_reps(3, 2, 2);
        let (pair_orbits, _) = enumerate_php_pair_orbits(3, 2, 2, &mono_orbits);
        assert_eq!(pair_orbits.len(), 4);
    }

    /// PHP_{5,4} d=5: existing engine reports 145 pair orbits.
    #[test]
    fn pair_orbit_count_php_5_4_d5() {
        let mono_orbits = enumerate_php_orbit_reps(5, 4, 5);
        let (pair_orbits, _) = enumerate_php_pair_orbits(5, 4, 5, &mono_orbits);
        eprintln!(
            "PHP_{{5,4}} d=5: {} mono orbits, {} pair orbits",
            mono_orbits.len(),
            pair_orbits.len()
        );
        assert_eq!(pair_orbits.len(), 145, "expected 145 pair orbits");
    }

    /// PHP_{7,6} d=7 measurement. Existing engine reports 1391 pair orbits,
    /// but may be off-by-small (its monomial_orbits reports 347 vs our 348).
    #[test]
    #[ignore]
    fn pair_orbit_count_php_7_6_d7() {
        let mono_orbits = enumerate_php_orbit_reps(7, 6, 7);
        let t = std::time::Instant::now();
        let (pair_orbits, _) = enumerate_php_pair_orbits(7, 6, 7, &mono_orbits);
        eprintln!(
            "PHP_{{7,6}} d=7: {} mono orbits, {} pair orbits in {:.3}s",
            mono_orbits.len(),
            pair_orbits.len(),
            t.elapsed().as_secs_f64()
        );
    }

    /// PHP_{8,7} d=7 measurement.
    #[test]
    #[ignore]
    fn pair_orbit_count_php_8_7_d7() {
        let mono_orbits = enumerate_php_orbit_reps(8, 7, 7);
        let t = std::time::Instant::now();
        let (pair_orbits, _) = enumerate_php_pair_orbits(8, 7, 7, &mono_orbits);
        eprintln!(
            "PHP_{{8,7}} d=7: {} mono orbits, {} pair orbits in {:.3}s",
            mono_orbits.len(),
            pair_orbits.len(),
            t.elapsed().as_secs_f64()
        );
    }

    /// PHP_{6,5} d=6: existing engine reports 450 pair orbits.
    #[test]
    fn pair_orbit_count_php_6_5_d6() {
        let mono_orbits = enumerate_php_orbit_reps(6, 5, 6);
        let (pair_orbits, _) = enumerate_php_pair_orbits(6, 5, 6, &mono_orbits);
        eprintln!(
            "PHP_{{6,5}} d=6: {} mono orbits, {} pair orbits",
            mono_orbits.len(),
            pair_orbits.len()
        );
        assert_eq!(pair_orbits.len(), 450, "expected 450 pair orbits");
    }

    /// End-to-end: PHP_{6,5} d=6 over 𝔽_7. Existing engine: 3.9s total.
    #[test]
    #[ignore]
    fn end_to_end_php_6_5_d6_f7() {
        let (_, axioms) = crate::problems::php_functional(6, 5, 7);
        let t = std::time::Instant::now();
        let mults = find_php_orbit_cert(6, 5, 6, 7).expect("expected cert at d=6");
        eprintln!(
            "PHP_{{6,5}} d=6 𝔽_7: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        let mut acc = PolyP::zero(7);
        for (&ai, mult) in &mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        assert!(acc.is_one(), "cert does not verify");
    }

    /// End-to-end: PHP_{9,8} d=8 over 𝔽_11. Beyond existing engine's
    /// demonstrated reach (PHP_{8,7} d=8 was "conceivable, not measured").
    #[test]
    #[ignore]
    fn end_to_end_php_9_8_d8_f11() {
        let (_, axioms) = crate::problems::php_functional(9, 8, 11);
        let t = std::time::Instant::now();
        let mults = find_php_orbit_cert(9, 8, 8, 11).expect("expected cert at d=8");
        eprintln!(
            "PHP_{{9,8}} d=8 𝔽_11: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        let mut acc = PolyP::zero(11);
        for (&ai, mult) in &mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        assert!(acc.is_one(), "cert does not verify");
    }

    /// Small diagnostic: PHP_{8,7} d=8 to see if higher slack gives a cert.
    /// If this works but d=7 fails, my d=7 closure is too strict.
    #[test]
    #[ignore]
    fn end_to_end_php_8_7_d8_f11() {
        let t = std::time::Instant::now();
        let (_, axioms) = crate::problems::php_functional(8, 7, 11);
        let mults = find_php_orbit_cert(8, 7, 8, 11).expect("expected cert at d=8");
        eprintln!(
            "PHP_{{8,7}} d=8 𝔽_11: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        let mut acc = PolyP::zero(11);
        for (&ai, mult) in &mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        assert!(acc.is_one(), "cert does not verify");
    }

    /// Cross-check closed-form vs BFS scatter.
    #[test]
    fn scatter_methods_agree_small_cases() {
        for &(p, h, d, prime) in &[
            (3u32, 2u32, 2u32, 5u8),
            (5, 4, 5, 7),
            (5, 4, 6, 7),
            (6, 5, 6, 7),
            (6, 5, 7, 7),
            (6, 5, 7, 11),
            (6, 5, 8, 7),
        ] {
            let (disagreements, first) = compare_scatter_methods(p, h, d, prime);
            if let Some((r, c, cf, bfs)) = first {
                eprintln!(
                    "PHP_{{{},{}}} d={} 𝔽_{}: {} disagreements, first at ({}, {}): closed={} bfs={}",
                    p, h, d, prime, disagreements, r, c, cf, bfs
                );
            }
            assert_eq!(disagreements, 0, "PHP_{{{},{}}} d={} mismatch", p, h, d);
        }
    }

    /// Cross-check at d=7 for PHP_{7,6}, PHP_{8,7}.
    #[test]
    #[ignore]
    fn scatter_methods_agree_d7() {
        for &(p, h, d, prime) in &[(7u32, 6u32, 7u32, 11u8)] {
            let (disagreements, first) = compare_scatter_methods(p, h, d, prime);
            if let Some((r, c, cf, bfs)) = first {
                eprintln!(
                    "PHP_{{{},{}}} d={}: {} disagreements, first at ({}, {}): closed={} bfs={}",
                    p, h, d, disagreements, r, c, cf, bfs
                );
            }
            assert_eq!(disagreements, 0);
        }
    }

    /// Diagnostic: find smallest failing case.
    #[test]
    fn diagnostic_sweep_end_to_end() {
        let cases: &[(u32, u32, u32, u8)] = &[
            (5, 4, 5, 7),
            (5, 4, 6, 7),
            (6, 5, 6, 7),
            (6, 5, 7, 7),
            (6, 5, 8, 7),
            (7, 6, 7, 11),
            (6, 5, 7, 11),
            (7, 6, 8, 11),
            (7, 6, 6, 11),
            (8, 7, 6, 11), // d below closing
        ];
        for &(p, h, d, prime) in cases {
            let (_, axioms) = crate::problems::php_functional(p, h, prime);
            match find_php_orbit_cert(p, h, d, prime) {
                Some(mults) => {
                    let mut acc = PolyP::zero(prime);
                    for (&ai, mult) in &mults {
                        acc.add_assign(&mult.mul(&axioms[ai]));
                    }
                    if acc.is_one() {
                        eprintln!(
                            "PHP_{{{},{}}} d={} 𝔽_{}: ✓ {} mults, verifies",
                            p, h, d, prime, mults.len()
                        );
                    } else {
                        eprintln!(
                            "PHP_{{{},{}}} d={} 𝔽_{}: ✗ {} mults, cert FAILS verify",
                            p, h, d, prime, mults.len()
                        );
                    }
                }
                None => {
                    eprintln!("PHP_{{{},{}}} d={} 𝔽_{}: NO CERT", p, h, d, prime);
                }
            }
        }
    }

    /// End-to-end: PHP_{8,7} d=7 over 𝔽_11. Existing engine: ~14 min.
    #[test]
    #[ignore]
    fn end_to_end_php_8_7_d7_f11() {
        let (_, axioms) = crate::problems::php_functional(8, 7, 11);
        let t = std::time::Instant::now();
        let mults = find_php_orbit_cert(8, 7, 7, 11).expect("expected cert at d=7");
        eprintln!(
            "PHP_{{8,7}} d=7 𝔽_11: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        let mut acc = PolyP::zero(11);
        for (&ai, mult) in &mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        assert!(acc.is_one(), "cert does not verify");
    }

    /// End-to-end: PHP_{7,6} d=7 over 𝔽_11. Existing engine: 292s total.
    #[test]
    #[ignore]
    fn end_to_end_php_7_6_d7_f11() {
        let (_, axioms) = crate::problems::php_functional(7, 6, 11);
        let t = std::time::Instant::now();
        let mults = find_php_orbit_cert(7, 6, 7, 11).expect("expected cert at d=7");
        eprintln!(
            "PHP_{{7,6}} d=7 𝔽_11: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        let mut acc = PolyP::zero(11);
        for (&ai, mult) in &mults {
            acc.add_assign(&mult.mul(&axioms[ai]));
        }
        assert!(acc.is_one(), "cert does not verify");
    }

    /// End-to-end: find an NS cert for PHP_{5,4} d=5 over 𝔽_7. Multiply
    /// back and verify = 1.
    #[test]
    fn end_to_end_php_5_4_d5_f7() {
        let (_, axioms) = crate::problems::php_functional(5, 4, 7);
        let t = std::time::Instant::now();
        let mults = find_php_orbit_cert(5, 4, 5, 7).expect("expected cert at d=5");
        eprintln!(
            "PHP_{{5,4}} d=5 𝔽_7: cert with {} multipliers in {:.3}s",
            mults.len(),
            t.elapsed().as_secs_f64()
        );
        // Verify: Σ mults[i] · axioms[i] == 1 (polynomial identity).
        let mut acc = PolyP::zero(7);
        for (&ai, mult) in &mults {
            let contrib = mult.mul(&axioms[ai]);
            acc.add_assign(&contrib);
        }
        assert!(acc.is_one(), "cert does not verify: Σ mults · axioms != 1");
    }
}
