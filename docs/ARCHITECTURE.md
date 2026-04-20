# Cascade Solver — Architecture & Internals

This document describes how cascade works at the algorithmic and
implementation level, with pointers into the source. It is aimed at:

* **Reviewers** checking correctness claims — each subsystem has a
  stated soundness guarantee and a file:line pointer.
* **Extenders** adding a new problem family, a new characteristic, or
  a new proof-system output format.
* **Users** who want more detail than [TUTORIAL.md](TUTORIAL.md)
  provides.

The solver is ~15k lines of Rust; the algebraic pipeline described here
is ~3.5k lines concentrated in `src/algebra/`, `src/tuple_schema.rs`,
and `src/problems.rs`.

---

## Table of contents

1. [Scope and design philosophy](#1-scope-and-design-philosophy)
2. [End-to-end pipeline](#2-end-to-end-pipeline)
3. [Variable-tuple schema](#3-variable-tuple-schema)
4. [Polynomial representation](#4-polynomial-representation)
5. [Colex perfect-hash indexing](#5-colex-perfect-hash-indexing)
6. [Orbit-reduced NS engine](#6-orbit-reduced-ns-engine)
7. [Problem families](#7-problem-families)
8. [Certificate format and verifier](#8-certificate-format-and-verifier)
9. [VeriPB lowering](#9-veripb-lowering)
10. [CLI reference](#10-cli-reference)
11. [Performance characteristics](#11-performance-characteristics)
12. [Extending the solver](#12-extending-the-solver)
13. [Soundness and trust chain](#13-soundness-and-trust-chain)
14. [Limitations](#14-limitations)
15. [Glossary](#15-glossary)

---

## 1. Scope and design philosophy

### What cascade proves

Given a structured boolean formula `φ(x_1, ..., x_n)` encoded as
polynomial axioms `A_1, ..., A_m` over 𝔽_p (each `A_i ≡ 0` being a
constraint), cascade searches for a **Nullstellensatz certificate**:
polynomials `m_1, ..., m_m` of bounded total degree such that

```
∑_i m_i(x) · A_i(x)  ≡  1   (mod p,  mod ⟨x_v² − x_v⟩_v)
```

The existence of such a cert proves the `A_i` are jointly infeasible
over Boolean values: if any assignment satisfied all axioms, the LHS
would be `0`, contradicting `1`.

The degree bound `d` is the search budget — the tool looks for a cert
at that degree and reports success or "no cert at this degree / prime".

### What cascade exploits

Combinatorial formulas often have large automorphism groups. If a cert
exists at all at degree `d`, then one exists that is **G-invariant**:
a fixed-point under the group action. That invariant cert's search
space is the orbit-reduced quotient, which can be exponentially
smaller.

Example: PHP_{7,6} has `|G| = 7! · 6! = 3 628 800` symmetries. The
dense search space at `d = 7` has ≈33 M monomials; the orbit-reduced
space has 347. That's the heart of the approach.

### Precondition for orbit reduction: `p ∤ |G|`

If the prime `p` divides `|G|`, averaging over the group can kill the
cert: `(1/|G|) ∑_{g∈G} g·cert` is either another cert (if `|G|` is
invertible mod `p`) or zero. So orbit reduction is useful when `p ∤
|G|`, and falls back to the dense engine otherwise.

For PHP_{P,H}, this means `p ∉ {primes dividing P! · H!}`. For
Ramsey K_n, `p > n`. For Count_q at `p = q`, orbit reduction fails and
we use the dense path (`--alg-no-orbit`).

### Out of scope

* **Industrial SAT**. The orbit search pays off only when symmetry is
  substantial; random industrial instances don't have it.
* **Ramsey.** Nullstellensatz degree for Ramsey is Ω(n); no fixed-d
  cert exists. Cascade still has Ramsey tooling via the CDCL legs, but
  the algebraic path in this document is not the right match.
* **P vs NP / complexity-theoretic claims.** The polynomial-size NS
  proofs of PHP etc. are well-known properties of a stronger proof
  system than resolution. The contribution is the pipeline, not the
  existence of these proofs.

---

## 2. End-to-end pipeline

```
┌────────────────────────────────────────────────────────────────────┐
│                                                                    │
│    CLI args  ──►  dispatch  ──►  {dense|orbit} NS engine  ──►      │
│                                                                    │
│                                            │                       │
│                                  cert (Option<Map<i, Poly>>)       │
│                                            │                       │
│                             ┌──────────────┼──────────────┐        │
│                             ▼              ▼              ▼        │
│                        .cert file    .opb + .pbp    s UNSAT/SAT    │
│                             │              │                       │
│                             ▼              ▼                       │
│                 cascade_cert_verify    veripb (external)           │
│                             │              │                       │
│                             ▼              ▼                       │
│                         s VERIFIED    s VERIFIED UNSATISFIABLE     │
│                                                                    │
└────────────────────────────────────────────────────────────────────┘
```

* Entry: `src/main.rs` (CLI + dispatch).
* Dense path: `src/algebra/ns_fp.rs::find_ns_p_from_axioms` —
  enumerates all monomials up to `d`, solves linear system over 𝔽_p.
* Orbit path: `src/algebra/orbit_ns.rs::find_orbit_cert_fp_with_gens`
  — orbit-reduced, the subject of the rest of this document.
* Cert emit: `src/algebra/ns_cert.rs::CertDoc::write`.
* Cert verify: `src/bin/cascade_cert_verify.rs`, using
  `CertDoc::parse` + `CertDoc::verify` from the same module.
* VeriPB emit: `src/algebra/ns_to_pb.rs::emit_veripb`.

---

## 3. Variable-tuple schema

`src/tuple_schema.rs`. The schema is a small abstraction that decouples
orbit-reduced NS from any specific problem: problems produce axioms
over a named tuple space, and the engine enumerates and reduces
without caring about the problem semantics.

### The three pieces

```rust
// src/tuple_schema.rs:55
pub struct TupleVarSchema {
    pub bases: Vec<BaseSet>,
    pub tuple_kind: TupleKind,
    pub group: GroupSpec,
}
```

* **`bases`** — one or more finite sets, each with a name and size.
  PHP has `[BaseSet("P", n_pigeons), BaseSet("H", n_holes)]`; Ramsey
  has `[BaseSet("V", n)]`.

* **`tuple_kind`** — how to interpret variable identities as tuples
  over the bases:
  * `Ordered` — each variable is an ordered tuple `(a_1, ..., a_k)`
    with `a_i` ranging over base `i`. Variable count = `∏|b_i|`.
    Used by PHP.
  * `UnorderedPair` — each variable is an unordered pair `{a, b}`
    from one base. Variable count = `C(|base|, 2)`. Used by Ramsey
    and by Tseitin on graphs.
  * `UnorderedSubset { size: k }` — each variable is an unordered
    `k`-subset from one base. Variable count = `C(|base|, k)`.
    Used by Count_q.

* **`group`** — how the symmetry group acts on variables:
  * `FullProduct` — the direct product `S_{|b_1|} × ... × S_{|b_k|}`,
    with each factor permuting its base independently. Used by PHP.
  * `Diagonal` — a single `S_n` (one permutation), applied uniformly
    to every coordinate. Used by Ramsey, Count_q, Tseitin.

### Ranking / unranking

Each `(tuple_kind, group)` combination defines a bijection between
variable ids `1..=n_vars` and tuples / subsets. Ranking formulas live
in `src/tuple_schema.rs:78` onward:

| Kind | Formula |
|---|---|
| `Ordered` | Radix encoding: `v = 1 + ∑_i (t_i − 1) · ∏_{j>i} |b_j|` |
| `UnorderedPair` | Lex rank (kept for backward compat with Ramsey) |
| `UnorderedSubset{k}` | Colex rank: `v = 1 + ∑_{i=1..k} C(a_i − 1, i)` |

The colex formulation for `k`-subsets is the same combinatorial number
system used inside the orbit engine (see §5) — reusing the same
formula keeps enumeration and indexing consistent.

### Generator enumeration

`schema.generators()` at `src/tuple_schema.rs:138` returns the list of
**adjacent-transposition generators** for the schema's group:

* `FullProduct`: for each base `i` and each adjacent pair `(j, j+1)`,
  the permutation that swaps `j ↔ j+1` in base `i` and fixes all
  other bases. Total count = `∑ (|b_i| − 1)`.
* `Diagonal`: the same permutation is applied to every coordinate.
  Count = `|base_0| − 1`.

For example: PHP_{7,6} gets `6 + 5 = 11` generators (6 for pigeon
swaps, 5 for hole swaps); Count_3 on `[5]` gets `4` generators.

### Action on a variable

`schema.apply_var(v, g)` (`src/tuple_schema.rs:169`) applies a
generator to a variable id:

1. Decode `v` to its tuple via `tuple_of_var`.
2. Apply the per-base permutation `g.perms[i]` to each coordinate.
3. Re-encode via `var_of_tuple`.

For `UnorderedSubset` the coordinates are always sorted before
re-encoding, so the subset representation stays canonical.

The engine uses `var_action_table(g)` (`src/tuple_schema.rs:233`) —
the array `[g(1), g(2), ..., g(n)]` precomputed once per generator.
This turns `apply_var` into a single array lookup in the hot loop.

---

## 4. Polynomial representation

### Multilinear monomials

Boolean constraints are reduced modulo `x_v² − x_v`, so every monomial
is a *multilinear* product of distinct variables. Implementation in
`src/algebra/poly.rs`:

```rust
pub struct Monomial(pub BTreeSet<u32>);  // sorted variable support
```

The `BTreeSet` form is canonical and hashes consistently, but it's
allocation-heavy. The orbit engine converts to a compact bitmask form
for the hot path.

### u128 bitmask form

`src/algebra/orbit_ns.rs:31`:

```rust
type MonoBits = u128;         // bit v-1 set iff variable v in support
```

* `mono_to_bits(m, n)`: `BTreeSet` → `u128`, sets one bit per variable.
* `bits_to_mono(b)`: `u128` → `BTreeSet`, used only at cert
  reconstruction time.
* `apply_bits(b, var_table)`: apply a generator by iterating set bits
  and mapping each to its image via `var_table`. `O(popcount(b))` bit
  operations — typically ≤ `d` iterations.
* Degree via `b.count_ones()`; product of two multilinear monomials
  via `a | b` (disjoint support required, else degree grows).

The 128-bit cap covers every family with `n_vars ≤ 128`. In practice
PHP up to `P · H = 128` (e.g. `PHP_{11,11}`, `PHP_{13,9}`) and Ramsey
up to `n = 16` (120 edges). The cap is asserted at
`src/algebra/orbit_ns.rs:472` (inside `find_orbit_cert_fp_with_gens`):

```rust
assert!(n <= 128, "orbit_ns currently supports up to 128 vars (got {}).
    Bitmask Monomial is u128; widen to [u64; 4] for larger families.", n);
```

Widening to `[u64; 4]` is mechanical; we have not needed it yet.

### `PolyP` — polynomials over 𝔽_p

`src/algebra/ns_fp.rs`:

```rust
pub struct PolyP {
    pub p: u8,
    pub terms: BTreeMap<Monomial, u8>,  // coef in 0..p
}
```

Multilinear polynomial with coefficients in `0..p`. Methods:

* `add_assign`, `mul` — the usual ring operations with modular reduction.
* `degree()` — `max(monomial.0.len())`.
* `is_one()` — used by the in-solver self-check after cert synthesis.

---

## 5. Colex perfect-hash indexing

This is the critical data-structure decision for the orbit engine, so
it gets its own section.

### The problem

The engine enumerates all `(n choose ≤ d)` multilinear monomials and
repeatedly needs to map `u128` bits → enumeration index. The natural
choice — `HashMap<u128, usize>` — was the dominant memory cost:
~1.5 GB at PHP_{7,6} scale, ~15–20 GB at PHP_{8,7}.

### The solution

Colex ranking. For a monomial `S = {a_1 < a_2 < ... < a_k}` encoded as
bits, its position within the enumeration (grouped by degree, colex
within each degree) is given by:

```
rank(S) = prefix[k] + ∑_{i=1..k} C(a_i − 1, i)
```

where `prefix[k] = ∑_{k'=0..k-1} C(n, k')` is the cumulative count of
all smaller-degree monomials.

`src/algebra/orbit_ns.rs:138` — the `ColexIndex` struct holds:

* `binom: Vec<Vec<u32>>` — `binom[a][k] = C(a, k)`, size `(n+2)(d+2)`.
* `prefix: Vec<u32>` — length `d + 2`.

Total memory: a few KB. Independent of `n_monos`.

### `rank`: bits → index

`src/algebra/orbit_ns.rs:181`:

```rust
fn rank(&self, bits: MonoBits) -> u32 {
    let k = bits.count_ones();
    let mut r = self.prefix[k as usize];
    let mut b = bits;
    let mut i: u32 = 1;
    while b != 0 {
        let v = b.trailing_zeros();       // 0-indexed bit position
        r += self.binom[v as usize][i as usize];
        b &= b - 1;
        i += 1;
    }
    r
}
```

`O(d)` table lookups. No allocation.

### `unrank`: index → bits

`src/algebra/orbit_ns.rs:196`:

```rust
fn unrank(&self, r: u32) -> MonoBits {
    // Find degree k via prefix binary search / scan.
    // For each i = k, k-1, ..., 1: find largest a with C(a, i) <= rem.
    // a_i = a + 1; rem -= C(a, i).
}
```

Also `O(d)` — one inner while-loop per peeled element, each bounded by
`n`.

### Enumeration order

The monomial vector `monos_bits` must satisfy `monos_bits[i] ==
colex.unrank(i)`. Enumeration is done in colex order by degree
(`src/algebra/orbit_ns.rs:111`):

```rust
fn enumerate_bits_up_to(n: u32, d: usize) -> Vec<MonoBits> {
    fn rec(max_val, k_left, bits, out) { ... }
    let mut out = Vec::new();
    for k in 0..=d { rec(n, k, 0, &mut out); }
    out
}
```

For `k = 2, n = 4` the colex sequence is
`{1,2}, {1,3}, {2,3}, {1,4}, {2,4}, {3,4}` — larger elements vary
slowest. This matches the `rank` formula.

### Correctness test

`src/algebra/orbit_ns.rs:221` — `colex_tests::rank_matches_enumeration`
verifies the bijection for `n ∈ {3, 5, 7, 10}`, `d ∈ {1, 2, 3, 4}`:

```rust
let enum_bits = enumerate_bits_up_to(n, d as usize);
let ci = ColexIndex::new(n, d);
for (i, &b) in enum_bits.iter().enumerate() {
    assert_eq!(ci.rank(b) as usize, i);
    assert_eq!(ci.unrank(ci.rank(b)), b);
}
```

### Measured impact

PHP_{7,6} d=7: HashMap was 17 GB (out of 22.6 total); ColexIndex is
a few KB. Total RAM dropped from 3.05 GB (post-Stage-1) to 886 MB.

PHP_{8,7} d=7: HashMap would have been ~18 GB; ColexIndex is again a
few KB. Total RAM dropped from 22.8 GB to 5.5 GB.

---

## 6. Orbit-reduced NS engine

`src/algebra/orbit_ns.rs::find_orbit_cert_fp_with_gens` (line 458).
This is the main entry point; `find_orbit_cert_fp` is a thin wrapper
that uses `schema.generators()` as the default group.

### Phase 1: monomial enumeration

```rust
let monos_bits: Vec<MonoBits> = enumerate_bits_up_to(n, d);
let colex = ColexIndex::new(n, d as u32);
```

Colex order; the index is built once and reused.

### Phase 2: variable action tables

```rust
let var_tables: Vec<Vec<u32>> =
    gens.iter().map(|g| schema.var_action_table(g)).collect();
```

`var_tables[gi][v] = g_i(v)` for `v = 1..=n`. Small (few KB).
The previously-precomputed `mono_action[gi][mi]` (expensive —
14 GB at PHP_{8,7} scale) was dropped in favor of on-the-fly
`apply_bits + colex.rank` in the hot loop.

### Phase 3: monomial orbits

`monomial_orbits_on_the_fly` at `src/algebra/orbit_ns.rs:253`. BFS
over the monomial set. For each unvisited monomial `mi`:

* Start a new orbit; assign `orbit_id[mi]`.
* For each generator `g_i`, image is
  `colex.rank(apply_bits(monos_bits[mi], var_tables[gi]))`.
* Push unvisited images onto the BFS queue, assign same orbit id.

Output: `(orbit_id, orbit_rep)`. `orbit_id[mi]` is the orbit
number; `orbit_rep[orbit]` is the smallest monomial index in that
orbit (canonical representative).

`n_monos × n_gens` hash lookups in the original; now `n_monos ×
n_gens` colex ranks — same complexity, trivial constant factors,
no memory.

### Phase 4: axiom action under the group

`axiom_action_table(schema, axioms, gens)` at
`src/algebra/orbit_ns.rs:322`. For each generator `g` and axiom `A_i`,
applies `g` to every monomial in `A_i`, reconstructs the image
polynomial, looks up its index in the axiom list.

**Panic on non-closure.** If `g · A_i` is not syntactically equal to
any `A_j` in the axiom set, the engine panics with

```
axioms not closed under group action
```

This is the contract: problem factories must produce a group-closed
axiom set. For PHP, Count_q, Tseitin (on complete/regular graphs with
uniform charge), this is guaranteed by construction.

### Phase 5: unknown-orbit enumeration + matrix scatter

This is the dominant phase by time. The "unknowns" are pairs `(i,
μ_idx)` — axiom index × multiplier monomial index. Each unknown
corresponds to one scalar coefficient in the NS cert:

```
cert = ∑_i A_i · (∑_μ  c_{i,μ}  μ)
```

Under the group, these unknowns group into orbits. We enumerate
orbits (not individual pairs) — one column per orbit in the matrix.

`src/algebra/orbit_ns.rs:567` onward:

```rust
let mut pair_visited: Vec<u64> = vec![0u64; (n_axioms * n_monos).div_ceil(64)];
let mut unknown_seeds: Vec<(u32, u32)> = Vec::new();
let mut matrix_rows: Vec<Vec<u8>> = (0..n_mono_orbits).map(|_| Vec::new()).collect();

for each (i, mi) in lex order:
    if already visited: skip
    mark visited
    allocate new matrix column `col`, extend all rows by 0
    push seed (i, mi) to unknown_seeds[col]
    scatter (i, mi) into matrix column col
    BFS: for each generator, apply to (ci, cmi), get (ni, nmi).
        If unvisited: mark, scatter, enqueue.
```

Key performance properties:

* **Bit-packed visited set.** `pair_visited` is `1 bit per (axiom,
  monomial)` slot. At PHP_{7,6} d=7 this is 550 MB (vs 17 GB as
  `Vec<u32>`).
* **Members not materialized.** We store only one `seed` per orbit.
  The full member list is re-enumerated on demand during cert
  reconstruction (§ 6 Phase 7).
* **Fused scatter.** As each pair is visited we scatter its
  axiom-term contributions directly into the growing matrix, in one
  pass:

  ```rust
  fn scatter_pair(...) {
      let mu_bits = monos_bits[mi];
      for each (term_bits, coef) in axiom_bits[ai]:
          let product = term_bits | mu_bits;
          if product.count_ones() > d: skip
          let idx = colex.rank(product);
          let row = mono_orbit_id[idx];
          if idx == mono_orbit_rep[row]:             // canonical only
              matrix[row][col] += coef  (mod p)
  }
  ```

  Only canonical-representative monomial rows accumulate — this is
  where the row-space reduction happens.

### Phase 6: Gaussian elimination

`src/algebra/orbit_ns.rs:704`. Standard row-reduction over 𝔽_p with a
column-by-column pivot scan. Works on the `(n_mono_orbits) ×
(n_unknown_orbits + 1)` matrix where the last column is the RHS: `1`
in the row of the orbit containing the constant monomial (`bits =
0`, always colex rank 0), `0` elsewhere.

After elimination:

* If any row has all-zero LHS and nonzero RHS: **inconsistent**,
  return `None` ("no cert at this degree"). Prints
  `TOTAL (no cert, inconsistent): X.Xs` in verbose mode.
* Otherwise: extract scalar `solution[col]` for each unknown orbit,
  proceed to reconstruction.

### Phase 7: cert reconstruction

`src/algebra/orbit_ns.rs:770`. For each nonzero `solution[col]`:

1. Retrieve `seed = unknown_seeds[col]`.
2. Call `reenumerate_orbit_members(monos_bits, colex, var_tables,
   axiom_action, n_axioms, seed)` at line 389: BFS in the pair-space
   from `seed`, returns all `(ai, mi)` pairs in that orbit.
3. For each member, add `solution[col] · monos_bits[mi]` to
   `mults[ai]` (accumulating into the multiplier polynomial for axiom
   `ai`).

Output: `BTreeMap<usize, PolyP>` — a multiplier polynomial per axiom
with nonzero contribution.

### Phase 8: in-solver verification

```rust
let mut acc = PolyP::zero(p);
for (&ai, mult) in &mults {
    acc.add_assign(&mult.mul(&axioms[ai]));
}
if !acc.is_one() { return None; }
```

Sanity check: the multiplier polynomials the engine just produced
really do reduce to `1` under polynomial multiplication. This catches
bugs in reconstruction. The independent `cascade_cert_verify` binary
(§ 8) does the same check externally after the cert is written to
disk.

### Complexity summary (conceptual)

| Phase | Cost | Memory |
|---|---|---|
| Monomial enumeration | `O(n_monos)` u128 ops | `n_monos × 16` B |
| ColexIndex build | `O(n · d)` | few KB |
| Monomial orbits | `O(n_monos · n_gens · d)` | `n_monos × 4` B orbit_id |
| Axiom action | `O(n_axioms · n_gens · avg_terms)` | `n_gens × n_axioms × 8` B |
| Pair BFS + scatter | `O(n_axioms · n_monos · n_gens · avg_terms)` | `n_axioms · n_monos / 8` B (bitset) + matrix |
| Gauss | `O(n_mono_orbits² · n_unknown_orbits)` (worst case) | matrix |
| Reconstruction | `O(active_orbits · orbit_size)` | small |

The pair BFS dominates at PHP scale. Gauss is nearly free because
the orbit-reduced matrix is tiny (a few hundred × a few thousand).

---

## 7. Problem families

`src/problems.rs` — the factory library. Each factory returns
`(TupleVarSchema, Vec<PolyP>)`, which is consumed directly by the
orbit engine.

### PHP (functional encoding) — `php_functional`

`src/problems.rs:21`. Schema: ordered pairs `(p, h)` with `p ∈ [P]`,
`h ∈ [H]`. Group: `S_P × S_H`.

Axioms:
* `P` **pigeon totality** constraints: `∑_h x(p, h) − 1 = 0`, degree 1.
* `H · C(P, 2)` **at-most-one (AMO)** constraints: `x(p_1, h) · x(p_2,
  h) = 0`, degree 2.

Total axioms: `P + H · C(P, 2)`. UNSAT iff `P > H`.

**Why this works empirically.** The functional encoding captures
"pigeon maps to exactly one hole" as a single degree-1 equation per
pigeon. Compare to the clausal encoding (a single clause `x(p, 1) ∨
... ∨ x(p, H)` plus AMO), which has higher NS degree due to how
disjunctive encoding interacts with the characteristic.

### Count_q (modular counting) — `count_q_partition`

`src/problems.rs:182`. Schema: `UnorderedSubset { size: q }` on a
base of `n` vertices. Group: `Diagonal S_n`.

Axioms: one per vertex `v ∈ [n]`:
```
(∑_{S: v ∈ S}  x_S)  −  1  =  0
```

UNSAT iff `q ∤ n` (partition of `n` into `q`-blocks is impossible).

**Characteristic sensitivity.** Summing all `n` vertex axioms gives
`q · ∑_S x_S − n`. Over 𝔽_q (same characteristic): `q · ∑ x_S` is
identically 0, so the identity reduces to `−n`, which is nonzero when
`q ∤ n` → degree-1 cert. Over 𝔽_p with `p ≠ q`: the identity is
`q·∑ x_S = n`, valid only if `n ≡ 0 (mod p)`, so different-prime
cases need higher degree. Empirical degree-vs-characteristic table
in the README.

### Tseitin (graph-based) — `tseitin_graph`, `tseitin_kn`, `tseitin_cycle`, `tseitin_petersen`

`src/problems.rs:240` onward. Schema: `UnorderedPair` on the vertex
set. Group: `Diagonal S_n` (but this only closes the axiom set when
the graph is edge-transitive under `S_n` — i.e. K_n. See §12 on
extending to non-S_n automorphism groups).

Axioms: one per vertex:
```
(∑_{e ∋ v}  x_e)  −  c_v  =  0
```

where `c_v ∈ {0, 1}` is the charge. UNSAT over 𝔽_2 iff `∑_v c_v` is
odd (handshake lemma gives the cert at degree 1).

Variants:
* `tseitin_kn(n, charge, prime)` — all vertices with uniform charge.
  UNSAT iff `n · charge` is odd.
* `tseitin_cycle(n, charge, prime)` — cycle C_n, uniform charge.
* `tseitin_petersen(charges, prime)` — Petersen graph, per-vertex
  charges. With uniform charge 1, `∑ c_v = 10` (even) → SAT; the
  engine correctly returns "no cert".

### Ramsey (disjunctive encoding) — `ramsey_disjunctive`

`src/problems.rs:74`. For infrastructure / integration-test purposes
only. Ramsey NS degree is `Ω(n)`, so the algebraic path does not
actually solve Ramsey at interesting sizes. The CDCL + symmetry legs
in the rest of cascade handle Ramsey; this factory exists to verify
the generic engine works on an UnorderedPair / Diagonal combination.

---

## 8. Certificate format and verifier

### The format

`src/algebra/ns_cert.rs`. Plain text, one statement per line:

```
c Nullstellensatz certificate over F_7
c sum over i of mult[i] * axiom[i] = 1 (mod p, mod <x^2 - x>)
p 7
d 6
n 30
axiom 0
term 6
term 1 1
term 1 2
end
...
mult 0
term 2
end
...
```

* `p / d / n` — prime, degree (metadata), variable count.
* `axiom <i> ... end` — a polynomial axiom. One monomial per `term`
  line: `term <coef_in_[1,p)>  <var_1>  <var_2>  ...`. Empty
  variable list means the constant monomial.
* `mult <i> ... end` — multiplier polynomial for axiom `i`. Missing
  multipliers are implicitly 0.
* `c` prefix — comment, ignored.

Axioms are echoed into the cert so the file is self-contained: the
verifier does not need to re-derive them from the problem factory.

### Write path

`CertDoc::from_solver(...)` + `CertDoc::write(w)` at
`src/algebra/ns_cert.rs:52`. Called from `main.rs` when `--alg-cert
<path>` is set. Size:

| Instance | Cert size |
|---|---:|
| PHP_{5,4} d=5 | 52 KB |
| PHP_{6,5} d=6 | 1.0 MB |
| Count_3 n=4 d=1 | 580 B |

### Independent verification

`src/bin/cascade_cert_verify.rs` (60 lines, intentionally small).
Uses `CertDoc::parse` and `CertDoc::verify`:

```rust
fn verify(&self) -> Result<(), String> {
    let mut acc = PolyP::zero(self.prime);
    for (i, mult) in self.mults.iter().enumerate() {
        acc.add_assign(&mult.mul(&self.axioms[i]));
    }
    if acc.is_one() {
        Ok(())
    } else {
        Err(format!(
            "sum does not reduce to 1 (got {} nonzero terms)",
            acc.terms.len()
        ))
    }
}
```

* Output on success: `s VERIFIED`, exit 0.
* Output on arithmetic failure: `s REJECTED sum does not reduce to 1
  (got N nonzero terms)`, exit 1.
* Output on parse failure: `parse error at line N: <reason>`, exit 1.

### Tamper resistance

Three distinct attack surfaces:

1. **Syntactic tamper** (coef out of range `[1, p)`, malformed line):
   rejected at parse time. E.g. flipping `term 1 2 3` → `term 99 2 3`
   triggers `coef 99 out of range [1, 7)`.
2. **Semantic tamper** (valid coef, wrong value): rejected at math
   time. `term 6` → `term 2` on a PHP_{6,5} cert triggers `s REJECTED
   sum does not reduce to 1 (got 7326 nonzero terms)`.
3. **Structural tamper** (dropping or duplicating an axiom): rejected
   at math time for the same reason.

The reproducer (`scripts/reproduce.sh`) does a live stealth-tamper
test on every run.

---

## 9. VeriPB lowering

`src/algebra/ns_to_pb.rs`. An NS cert over 𝔽_p can be lowered to a
pseudo-Boolean proof that the stock `veripb` binary (community-
standard verifier) accepts — connecting cascade to existing proof-
checking infrastructure.

### Scope

First-pass implementation handles **linear axioms with variables of
coefficient ±1**. This covers Count_q (at any characteristic) and
Tseitin on regular graphs with uniform charge.

Out of scope for now:

* **Nonlinear axioms** (PHP's `x_i x_j = 0`). Lowering needs
  expansion into pairwise-clause form plus polynomial-multiplier
  handling in the proof.
* **Polynomial multipliers.** The current path uses a generic "sum-
  and-divide" proof that does not thread through the solver's cert
  multipliers. The trade-off is broader applicability (any family
  with uniform variable multiplicity in the axioms) at the cost of
  not witnessing the exact NS cert.

### Encoding axioms as PB

`LinPoly::from_polyp` at `src/algebra/ns_to_pb.rs:48`. For each PolyP
axiom, extract the linear integer form `∑ a_v x_v + c`, rejecting
nonlinear terms. Coefficients in `[0, p)` are re-signed to
`[−⌊p/2⌋, ⌊p/2⌋]` for readability.

An axiom `L(x) = 0` over integers becomes **two** PB constraints:

```
(GE)  +1 x_a +1 x_b ... >= RHS      # LHS ≥ 0
(LE)  -1 x_a -1 x_b ... >= -RHS     # LHS ≤ 0, encoded as ≥
```

Both directions are needed because PB "equals" is not a native
operation — only `≥`.

### The proof: sum-and-divide

`emit_veripb` at `src/algebra/ns_to_pb.rs:104`. Given that each
variable appears in `q` axioms with coefficient 1 (checked by
`axiom_variable_multiplicity` at line 193), the proof is:

```
1.  pol ge_1 ge_2 + ... ge_n +          # Sum GE: q·∑ x >= total_rhs
2.  pol le_1 le_2 + ... le_n +          # Sum LE: -q·∑ x >= -total_rhs
3.  pol {ge_sum} q d                    # Divide by q (rounded up)
4.  pol {le_sum} q d                    # Divide by q
5.  pol {ge_div} {le_div} +             # Add → 0 >= 1 iff q ∤ total_rhs
```

* **Step 3** uses VeriPB's `d` operator: division rounds RHS *up* in
  the `≥`-direction, so `q · ∑ x ≥ total_rhs` becomes `∑ x ≥
  ⌈total_rhs/q⌉`.
* **Step 4** similarly gives `-∑ x ≥ -⌊total_rhs/q⌋` (= `∑ x ≤
  ⌊total_rhs/q⌋`).
* **Step 5** sum gives `0 ≥ ⌈total_rhs/q⌉ − ⌊total_rhs/q⌋ = 1` when
  `q ∤ total_rhs`. Contradiction.

### CLI

`--alg-cert-pb <stem>`: on UNSAT emits `<stem>.opb` (formula) +
`<stem>.pbp` (proof). Validate externally with:

```bash
veripb <stem>.opb <stem>.pbp
```

Expected output: `s VERIFIED UNSATISFIABLE`, exit 0.

### Live-verified cells

The reproducer runs these end-to-end through external `veripb 3.0.1`:

| Family | `p` | veripb verdict |
|---|---|---|
| `count:4,3` | 3 | `s VERIFIED UNSATISFIABLE` |
| `count:5,3` | 3 | `s VERIFIED UNSATISFIABLE` |
| `count:5,2` | 2 | `s VERIFIED UNSATISFIABLE` |
| `count:7,2` | 2 | `s VERIFIED UNSATISFIABLE` |

---

## 10. CLI reference

Primary entry point: `target/release/cascade`. Verifier:
`target/release/cascade_cert_verify`.

### Flags for the algebraic pipeline

| Flag | Effect |
|---|---|
| `--alg-preprocess D` | Run an algebraic UNSAT probe at degree `D` before CDCL |
| `--alg-p P` | Prime for the algebraic probe (default `2`) |
| `--problem FAMILY[:args]` | Route through the generic orbit engine on a named family |
| `--alg-no-orbit` | Dense NS engine (no orbit reduction) — needed when `p ∣ |G|` |
| `--alg-cert <path>` | On UNSAT, write the NS cert in cascade format |
| `--alg-cert-pb <stem>` | On UNSAT, also write `<stem>.opb` + `<stem>.pbp` for VeriPB |
| `--alg-php P H` | Legacy path; functional PHP_{P,H} via PHP-specific engine |

Supported families for `--problem`:

```
--problem php:P,H
--problem ramsey:s,t,n
--problem count:n,q
--problem tseitin-kn:N[,c]
--problem tseitin-cycle:N[,c]
--problem tseitin-petersen
```

### Environment variables

| Variable | Effect |
|---|---|
| `CASCADE_ALG_TIMING=1` | Per-phase timing output (`c [alg-timing] ...`) on stderr |
| `CASCADE_SYM_DECIDE={N,full}` | Symmetry-aware decision heuristic depth (Ramsey / SAT legs; orthogonal to the algebraic path) |

### Exit codes

Inherited from the SAT solver convention:

| Code | Meaning |
|---|---|
| `10` | SATISFIABLE (model found) |
| `20` | UNSATISFIABLE (cert found) |
| `0` | Indeterminate / timed out / no algebraic cert at the given `(p, d)` |
| `2` | CLI error |

---

## 11. Performance characteristics

### PHP benchmark trajectory

Three sessions of work on the orbit engine:

| | Original | Stage 1 (b34a51a) | Colex (719537a) |
|---|---|---|---|
| PHP_{5,4} d=5, 𝔽₇ | 0.25 s / 10 MB | 0.17 s / 10 MB | 0.17 s / 10 MB |
| PHP_{6,5} d=6, 𝔽₇ | 22 s / 930 MB | 1.7 s / 69 MB | **0.98 s / 35 MB** |
| PHP_{7,6} d=7, 𝔽₁₁ | OOM | 260 s / 3.05 GB | **75 s / 886 MB** |
| PHP_{8,7} d=7, 𝔽₁₁ | timeout / 40 GB | 60 min / 22.8 GB | **14 min / 5.5 GB** |

PHP_{8,7} d=7 correctly returns "no cert" because PHP_{P, P-1}
requires `d ≥ P`; `d = 8` is the real frontier.

### Phase breakdown (PHP_{7,6} d=7, 𝔽₁₁)

From `CASCADE_ALG_TIMING=1` on current head:

```
enumerate_bits_up_to:  0.24 s   33.2M monomials
colex index build:     0.00 s   binom 44 × 9 = 396 entries
var_tables:            0.00 s   11 generators
monomial_orbits:      12.1 s   347 orbits from 33.2M
axiom_action_table:    0.00 s   133 axioms × 11 gens
unknown_orbits:       57.3 s   1391 orbits, 166M scatter pairs
gaussian elim:         0.01 s   347 × 1391
verify:                4.7 s
TOTAL:                75 s
```

Pair BFS + matrix scatter dominates (77 % of wall time). Monomial
orbits (16 %) is the next chunk.

### Memory inventory (PHP_{7,6} d=7, 𝔽₁₁)

```
monos_bits (Vec<u128>):          533 MB   (33M × 16B)
mono_orbit_id (Vec<u32>):        133 MB   (33M × 4B)
pair_visited bitset:             550 MB   ((133 × 33M) / 8)
matrix + misc:                     4 MB
ColexIndex (binom + prefix):      <1 KB
------------------------------------
peak ≈ 886 MB (measured via /usr/bin/time -v)
```

Previously: plus 1.4 GB `mono_action`, plus ~1.5 GB `bits_index`
HashMap, plus ~530 MB HashMap overhead. Both dropped now.

### Scaling considerations

* **`n_monos` grows as `∑_{k ≤ d} C(n, k)`.** For PHP_{P,H}: `n =
  P·H`, `d = P`. At PHP_{10,9}, `n = 90`, `d = 10`: `∑_{k ≤ 10} C(90,
  k) ≈ 10¹²`. Beyond enumeration; needs direct orbit enumeration
  (real research).
* **Pair BFS time scales as `n_axioms · n_monos · n_gens`.** At PHP
  scale the `n_axioms` factor is small (≤ 200), but `n_monos · n_gens`
  can be billions.
* **`|G|` controls orbit reduction efficiency.** Larger `|G|` →
  smaller orbits → fewer matrix columns. For PHP_{7,6}, `|G| = 7!·6!
  = 3.6M`; the 33M monomials collapse to 347 orbits, a factor of ≈
  95,000×.

---

## 12. Extending the solver

### Adding a new problem family

Minimal example (~50 LOC):

```rust
// src/problems.rs
pub fn my_family(n: u32, prime: u8) -> (TupleVarSchema, Vec<PolyP>) {
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("V", n)],
        tuple_kind: TupleKind::UnorderedPair,  // or Ordered / UnorderedSubset
        group: GroupSpec::Diagonal,            // or FullProduct
    };

    let mut axioms: Vec<PolyP> = Vec::new();
    // ... build axioms as PolyP over 𝔽_prime ...
    // Each axiom must be closed under schema.generators() !

    (schema, axioms)
}
```

Plus three lines in `src/main.rs`:

```rust
("my-family", [n]) => cascade::problems::my_family(*n, alg_prime),
```

And a test in `src/problems.rs` or a dedicated module:

```rust
#[test]
fn my_family_axioms_closed_under_group() {
    let (schema, axioms) = my_family(6, 3);
    let gens = schema.generators();
    // ... assert every g·A_i is another A_j ...
}
```

The engine will panic with `axioms not closed under group action` if
closure fails; designing the factory to be closed by construction is
easier than debugging after the fact.

### Adding a custom group (non-`S_n` automorphism)

For Tseitin on non-complete graphs (cycle, hypercube, Petersen), the
automorphism group is a proper subgroup of `S_n`. Use
`find_orbit_cert_fp_with_gens` directly and pass a custom generator
list:

```rust
// Build generators for, e.g., the dihedral group on a cycle:
let rot: Generator = Generator { perms: vec![(1..n).chain(std::iter::once(0)).collect()] };
let ref_: Generator = Generator { perms: vec![(0..n).rev().collect()] };
let gens = vec![rot, ref_];

let cert = cascade::algebra::orbit_ns::find_orbit_cert_fp_with_gens(
    &schema, &axioms, &gens, d, p,
);
```

The engine still requires `p ∤ |G|` for the group generated by your
custom gens, and still verifies closure.

### Adding a new characteristic

Nothing to do. `PolyP` works for any prime `p ≤ 251`
(`src/algebra/ns_fp.rs:367`). The modular-inverse table
(`src/algebra/orbit_ns.rs:346`) uses a brute-force search that is
fine for small primes; a precomputed table would be the appropriate
optimization if very large primes become interesting.

### Adding a new proof-output format

See `src/algebra/ns_to_pb.rs` as the template. Takes a `CertDoc` in
and writes bytes out via `dyn Write`. Register in
`src/algebra/mod.rs` and wire a CLI flag similar to `--alg-cert-pb`.

---

## 13. Soundness and trust chain

### Solver-internal soundness

`find_orbit_cert_fp_with_gens` computes a candidate cert via linear
algebra, then **verifies it in-solver** at
`src/algebra/orbit_ns.rs:799`:

```rust
let mut acc = PolyP::zero(p);
for (&ai, mult) in &mults {
    acc.add_assign(&mult.mul(&axioms[ai]));
}
if !acc.is_one() { return None; }
```

A bug in the orbit reduction or matrix scatter that produces an
incorrect cert is caught here — the solver refuses to report UNSAT
without the polynomial identity being reconstructed.

### External cert verification

Two independent verifiers:

1. **`cascade_cert_verify`** (`src/bin/cascade_cert_verify.rs`) —
   reads the cascade `.cert` file, rebuilds the polynomial identity
   using only `src/algebra/ns_cert.rs` and `src/algebra/ns_fp.rs`
   (no orbit engine code), confirms `∑ m_i · A_i ≡ 1`. The entire
   verifier is under 100 source lines of code; independent audit is
   feasible.

2. **`veripb`** — stock community checker for pseudo-Boolean proofs.
   Accepts our lowered `.opb + .pbp` output as `s VERIFIED
   UNSATISFIABLE`. Zero trust in cascade code.

The combination — cascade's own cert + external veripb acceptance —
gives a two-checker trust chain where a bug in one does not silently
produce a false UNSAT.

### What the solver DOES NOT claim

* **Certified completeness.** The solver searches for a cert at
  degree `d`; "no cert at degree d" does not mean the problem is SAT,
  only that the algebraic degree is higher than `d`. Report as
  indeterminate (exit 0), not SAT.
* **Optimality of the degree found.** The solver reports the `d`
  passed in. It does not search lower degrees automatically.
* **Any claim outside algebraic proof complexity.** The README's
  scope section explicitly calls this out.

---

## 14. Limitations

### Algorithmic

* **`n_vars ≤ 128`.** The `u128` monomial bitmask is hard-coded.
  Widening to `[u64; 4]` is mechanical (~20 LOC) but we have not
  needed it. PHP up to `P·H = 128` and Ramsey up to `n = 16` are in
  scope; anything larger needs the widen.
* **Integer monomial count ≤ 2³².** `mono_orbit_id: Vec<u32>` assumes
  `n_monos ≤ 2^32`. Only hits at PHP_{10, 9} d=10 scale; a widen to
  `u64` would push the ceiling by another `2^32`.
* **Direct orbit enumeration (not implemented).** At PHP_{10,9}
  scale the monomial space has ~10¹² elements and cannot be
  materialized even as bitmasks. A future version would enumerate
  orbits directly without per-monomial enumeration — real research.

### Infrastructure

* **Tseitin on non-regular graphs.** The `find_orbit_cert_fp_with_gens`
  hook exists, but the public `tseitin_*` factories currently always
  use `schema.generators()` (= full `S_n`). Custom-group wiring for
  hypercube, Petersen, etc. requires passing `Generator`s through
  the CLI — follow-up work.
* **PHP → VeriPB.** The current VeriPB lowering handles linear axioms
  only; PHP's AMO `x_i x_j = 0` is quadratic. A path forward is to
  expand AMO into pairwise clauses (`x_i + x_j ≤ 1`) and emit a
  cutting-planes-style proof; more involved than the sum-and-divide
  trick.
* **No CNF pattern auto-detection.** Running `cascade --alg-preprocess
  D my_php.cnf` on a raw PHP CNF falls into the dense 𝔽₂ path and
  does not auto-detect that `--problem php:P,H` would be faster.
  Straightforward follow-up.

### Scope

* **Not a SAT-competition entry.** The orbit engine is in a different
  proof system than resolution; direct comparison with Kissat is
  apples to oranges.
* **Not a general-purpose PB solver.** The VeriPB output is a thin
  skeleton that demonstrates the path, not a full PB-proof-search
  engine.

---

## 15. Glossary

| Term | Definition |
|---|---|
| **Nullstellensatz (NS) certificate** | A sum `∑ m_i · A_i ≡ 1` proving the axioms `A_i` have no common Boolean zero. |
| **Degree** | The maximum total degree of any term in a multiplier polynomial, i.e. the NS search budget. |
| **Characteristic (`p`)** | The prime modulus of the field 𝔽_p. Different `p` give different proof systems (modular reasoning). |
| **Multilinear** | Polynomials reduced modulo `x_v² − x_v`; every monomial is a product of *distinct* variables. |
| **Orbit** | Equivalence class under the group action. Monomial orbits and pair orbits are the two kinds that matter. |
| **Closure (under group action)** | The axiom set must map into itself under every group generator. Precondition for orbit reduction. |
| **Colex rank** | Position in the "colex" (colexicographic) enumeration of subsets; larger elements vary slowest. |
| **Perfect hash** | A deterministic function that assigns a unique index to each element with no collisions — here, `colex.rank`. |
| **Pseudo-Boolean (PB)** | Integer-coefficient linear inequality system over Boolean variables. VeriPB's native language. |
| **Tseitin encoding** | Encoding a polynomial (here, over 𝔽_2) as a set of XOR constraints — the original 1968 construction. |
| **PHP** | Pigeonhole principle: `P` pigeons in `H` holes with `P > H`. |
| **Count_q** | Modular counting principle: partition `[n]` into `q`-blocks (UNSAT iff `q ∤ n`). |

---

## Further reading (in-repo)

* [`README.md`](../README.md) — scope, published tables, build instructions.
* [`TUTORIAL.md`](TUTORIAL.md) — hands-on walkthrough from CNF to verified cert.
* `src/algebra/orbit_ns.rs` — the engine, ~870 lines, heavily commented.
* `src/algebra/ns_cert.rs` — cert format + in-solver verifier, ~450 lines.
* `src/algebra/ns_to_pb.rs` — VeriPB lowering, ~390 lines.
* `src/tuple_schema.rs` — schema abstraction, ~480 lines.
* `src/problems.rs` — problem factories, ~470 lines.

Total algebraic pipeline: ~3500 lines. The engine proper
(`orbit_ns.rs` + `tuple_schema.rs` + `problems.rs`) is ~1800 lines.
