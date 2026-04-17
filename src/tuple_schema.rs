//! Variable-tuple schema abstraction.
//!
//! Variables in structured SAT instances are k-tuples over a product of base
//! sets: Ramsey edges are unordered pairs over vertices, PHP variables are
//! ordered pairs (pigeon, hole), Sudoku cells are triples (row, col, digit).
//! A symmetry group acts by permuting base-set elements — `FullProduct` for
//! independent bases (PHP's S_P × S_H), `Diagonal` for bases-that-are-really-
//! the-same-set (Ramsey's single S_n on vertices).
//!
//! This abstraction decouples orbit-reduced NS from any specific problem:
//! the engine takes a schema + axioms and runs.

use std::collections::BTreeMap;

/// A named base set. Elements are 1-indexed `1..=size`.
#[derive(Clone, Debug)]
pub struct BaseSet {
    pub name: String,
    pub size: u32,
}

impl BaseSet {
    pub fn new<S: Into<String>>(name: S, size: u32) -> Self {
        Self {
            name: name.into(),
            size,
        }
    }
}

/// How variable tuples are encoded.
#[derive(Clone, Debug)]
pub enum TupleKind {
    /// Each variable = an ordered tuple `(a_1, ..., a_k)` with `a_i ∈ base_i`.
    /// Variable count = `∏ |base_i|`.
    Ordered,
    /// Each variable = an unordered pair `{a, b}` with `a < b`, from a single
    /// base. Variable count = `C(|base|, 2)`.
    UnorderedPair,
}

/// Group acting on variables by permuting base elements.
#[derive(Clone, Debug)]
pub enum GroupSpec {
    /// Full direct product `S_{|b_1|} × … × S_{|b_k|}`. Adjacent
    /// transpositions in each base are generators.
    FullProduct,
    /// Diagonal action — single `S_n` applied uniformly to all coordinates.
    /// For `UnorderedPair`, this is the natural S_n on vertices.
    /// For `Ordered`, requires all bases to have the same size.
    Diagonal,
}

#[derive(Clone, Debug)]
pub struct TupleVarSchema {
    pub bases: Vec<BaseSet>,
    pub tuple_kind: TupleKind,
    pub group: GroupSpec,
}

impl TupleVarSchema {
    pub fn n_vars(&self) -> u32 {
        match self.tuple_kind {
            TupleKind::Ordered => self.bases.iter().map(|b| b.size).product(),
            TupleKind::UnorderedPair => {
                assert_eq!(
                    self.bases.len(),
                    1,
                    "UnorderedPair requires exactly one base"
                );
                let n = self.bases[0].size;
                n * (n - 1) / 2
            }
        }
    }

    /// Encode a tuple as a 1-indexed variable id.
    pub fn var_of_tuple(&self, tup: &[u32]) -> u32 {
        match self.tuple_kind {
            TupleKind::Ordered => {
                assert_eq!(tup.len(), self.bases.len());
                let mut v: u32 = 0;
                for (i, &ti) in tup.iter().enumerate() {
                    debug_assert!(ti >= 1 && ti <= self.bases[i].size);
                    v = v * self.bases[i].size + (ti - 1);
                }
                v + 1
            }
            TupleKind::UnorderedPair => {
                assert_eq!(tup.len(), 2);
                let (a, b) = if tup[0] < tup[1] {
                    (tup[0], tup[1])
                } else {
                    (tup[1], tup[0])
                };
                let n = self.bases[0].size;
                let mut idx = 0u32;
                for i in 1..a {
                    idx += n - i;
                }
                idx += b - a - 1;
                idx + 1
            }
        }
    }

    /// Decode a 1-indexed variable id back to its tuple.
    pub fn tuple_of_var(&self, v: u32) -> Vec<u32> {
        match self.tuple_kind {
            TupleKind::Ordered => {
                let mut remainder = v - 1;
                let mut tup = vec![0u32; self.bases.len()];
                for i in (0..self.bases.len()).rev() {
                    let s = self.bases[i].size;
                    tup[i] = (remainder % s) + 1;
                    remainder /= s;
                }
                tup
            }
            TupleKind::UnorderedPair => {
                let mut idx = v - 1;
                let n = self.bases[0].size;
                for a in 1..n {
                    let width = n - a;
                    if idx < width {
                        return vec![a, a + 1 + idx];
                    }
                    idx -= width;
                }
                unreachable!("UnorderedPair var out of range")
            }
        }
    }

    /// Adjacent-transposition generators. Each generator is a list of per-base
    /// permutations (length = `bases.len()`), given as 0-indexed
    /// `perm[i]` = new position of element i+1.
    pub fn generators(&self) -> Vec<Generator> {
        let mut gens = Vec::new();
        match self.group {
            GroupSpec::FullProduct => {
                for (bi, base) in self.bases.iter().enumerate() {
                    for i in 0..base.size.saturating_sub(1) {
                        let mut perms: Vec<Vec<u32>> = self
                            .bases
                            .iter()
                            .map(|b| (0..b.size).collect())
                            .collect();
                        perms[bi].swap(i as usize, (i + 1) as usize);
                        gens.push(Generator { perms });
                    }
                }
            }
            GroupSpec::Diagonal => {
                let n = self.bases[0].size;
                for i in 0..n.saturating_sub(1) {
                    // All bases share the same permutation.
                    let mut p: Vec<u32> = (0..n).collect();
                    p.swap(i as usize, (i + 1) as usize);
                    let perms = vec![p; self.bases.len()];
                    gens.push(Generator { perms });
                }
            }
        }
        gens
    }

    /// Apply generator `g` to variable `v`, returning the new variable id.
    pub fn apply_var(&self, v: u32, g: &Generator) -> u32 {
        let tup = self.tuple_of_var(v);
        let new_tup: Vec<u32> = match self.tuple_kind {
            TupleKind::Ordered => tup
                .iter()
                .enumerate()
                .map(|(i, &t)| g.perms[i][(t - 1) as usize] + 1)
                .collect(),
            TupleKind::UnorderedPair => {
                // Single base (shared by both coords). Apply perms[0] uniformly.
                tup.iter()
                    .map(|&t| g.perms[0][(t - 1) as usize] + 1)
                    .collect()
            }
        };
        self.var_of_tuple(&new_tup)
    }
}

/// A single group element described by one permutation per base.
/// `perms[i][k]` = 0-indexed image of element `k+1` in base `i`.
#[derive(Clone, Debug)]
pub struct Generator {
    pub perms: Vec<Vec<u32>>,
}

impl Generator {
    /// Identity on the schema.
    pub fn identity(schema: &TupleVarSchema) -> Self {
        Self {
            perms: schema.bases.iter().map(|b| (0..b.size).collect()).collect(),
        }
    }

    /// Compose: `(a ∘ b)(x) = a(b(x))`.
    pub fn compose(&self, other: &Self) -> Self {
        let perms = self
            .perms
            .iter()
            .zip(other.perms.iter())
            .map(|(a, b)| b.iter().map(|&x| a[x as usize]).collect())
            .collect();
        Self { perms }
    }
}

// Provide Monomial helpers that act via a Generator on a BTreeSet-based
// Monomial (from algebra::poly). Kept here so clients of the schema don't
// need to re-derive the action.
use crate::algebra::poly::Monomial;

impl TupleVarSchema {
    pub fn apply_mono(&self, m: &Monomial, g: &Generator) -> Monomial {
        let mut s: std::collections::BTreeSet<u32> = std::collections::BTreeSet::new();
        for &v in &m.0 {
            s.insert(self.apply_var(v, g));
        }
        Monomial(s)
    }
}

// Token BTreeMap re-export so downstream modules can use it consistently.
pub(crate) type OrbitMap<K, V> = BTreeMap<K, V>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ordered_roundtrip_php() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("P", 5), BaseSet::new("H", 4)],
            tuple_kind: TupleKind::Ordered,
            group: GroupSpec::FullProduct,
        };
        assert_eq!(schema.n_vars(), 20);
        for p in 1..=5 {
            for h in 1..=4 {
                let v = schema.var_of_tuple(&[p, h]);
                let t = schema.tuple_of_var(v);
                assert_eq!(t, vec![p, h]);
            }
        }
    }

    #[test]
    fn unordered_pair_roundtrip_ramsey() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("V", 6)],
            tuple_kind: TupleKind::UnorderedPair,
            group: GroupSpec::Diagonal,
        };
        assert_eq!(schema.n_vars(), 15); // C(6, 2)
        for a in 1..=5 {
            for b in (a + 1)..=6 {
                let v = schema.var_of_tuple(&[a, b]);
                let t = schema.tuple_of_var(v);
                assert_eq!(t, vec![a, b]);
            }
        }
    }

    #[test]
    fn full_product_generator_count() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("P", 5), BaseSet::new("H", 4)],
            tuple_kind: TupleKind::Ordered,
            group: GroupSpec::FullProduct,
        };
        // (P-1) + (H-1) = 4 + 3 = 7 adjacent transpositions.
        assert_eq!(schema.generators().len(), 7);
    }

    #[test]
    fn diagonal_generator_count() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("V", 6)],
            tuple_kind: TupleKind::UnorderedPair,
            group: GroupSpec::Diagonal,
        };
        // (n - 1) = 5 adjacent transpositions on vertices.
        assert_eq!(schema.generators().len(), 5);
    }

    #[test]
    fn php_pigeon_swap_permutes_vars() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("P", 3), BaseSet::new("H", 2)],
            tuple_kind: TupleKind::Ordered,
            group: GroupSpec::FullProduct,
        };
        let gens = schema.generators();
        // First generator swaps pigeons 1 and 2. So var (1, h) ↔ var (2, h).
        let swap_p12 = &gens[0];
        let v11 = schema.var_of_tuple(&[1, 1]);
        let v21 = schema.var_of_tuple(&[2, 1]);
        assert_eq!(schema.apply_var(v11, swap_p12), v21);
        assert_eq!(schema.apply_var(v21, swap_p12), v11);
    }

    #[test]
    fn ramsey_vertex_swap_permutes_edge_vars() {
        let schema = TupleVarSchema {
            bases: vec![BaseSet::new("V", 4)],
            tuple_kind: TupleKind::UnorderedPair,
            group: GroupSpec::Diagonal,
        };
        let gens = schema.generators();
        // Swap vertices 1 and 2: edge {1,3} ↔ {2,3}.
        let g = &gens[0];
        let e13 = schema.var_of_tuple(&[1, 3]);
        let e23 = schema.var_of_tuple(&[2, 3]);
        assert_eq!(schema.apply_var(e13, g), e23);
    }
}
