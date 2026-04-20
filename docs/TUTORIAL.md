# Tutorial: from a combinatorial problem to a verified NS certificate

This walks you from an unfamiliar problem, through the cascade pipeline,
to an externally-verifiable Nullstellensatz certificate. Read top to
bottom for a 15-minute orientation; skim the headings if you know what
you want.

## Prerequisites

```bash
cargo build --release
```

Produces `target/release/cascade` (the solver) and
`target/release/cascade_cert_verify` (the independent cert checker).
No external binaries required for the core path.

## What cascade is good for

cascade attacks **combinatorial infeasibility problems** that have two
structural properties:

1. **Substantial group symmetry.** All pigeonholes are interchangeable;
   all vertices of K_n are interchangeable; all holes are
   interchangeable. The tool exploits this to shrink the proof search.
2. **Low algebraic proof degree over some `𝔽_p`.** The unsatisfiability
   has a short polynomial-identity certificate — typically for
   well-known combinatorial principles like PHP, Count_q, Tseitin.

If your problem has both, cascade can find a cert faster than a
general-purpose SAT solver *and* give you an object a third-party can
verify without running cascade.

If your problem has neither, a general-purpose SAT solver is probably
the right tool (Kissat, CaDiCaL).

## The one-minute example

Write a dummy placeholder CNF:

```bash
printf "p cnf 1 1\n1 0\n" > /tmp/dummy.cnf
```

Run PHP_{6,5} and emit + verify a certificate:

```bash
./target/release/cascade \
    --alg-preprocess 6 --alg-p 7 --problem php:6,5 \
    --alg-cert /tmp/php65.cert /tmp/dummy.cnf

./target/release/cascade_cert_verify /tmp/php65.cert
```

Expected:

```
c [alg] generic orbit 𝔽_7 cert at degree 6 in 0.98s, 81 axioms — UNSAT
c [alg-cert] wrote certificate to /tmp/php65.cert
s UNSATISFIABLE

c loaded: prime=7 degree=6 n_vars=30 axioms=81 nonzero_mults=81
s VERIFIED
```

The `s VERIFIED` line is from the independent checker. It reads the
cert file and reconstructs the polynomial identity `∑ m_i · A_i ≡ 1`
from scratch; it does not call into the solver.

## Problem families

### PHP (pigeonhole principle)

`--problem php:P,H` — encode the functional PHP asking whether `P`
pigeons fit in `H` holes where each pigeon picks exactly one hole.
UNSAT iff `P > H`.

* Works up to roughly PHP_{7,6} (30 vars, d=7) in under 2 minutes and
  ~1 GB. PHP_{8,7} d=8 is the current open frontier.
* Choose the prime as the smallest `p` with `p ∤ P! · H!`. For PHP_{7,6}
  this is `p = 11`; for PHP_{5,4} it's `p = 7`. Too-small primes return
  "no cert" because `p ∣ |G|` breaks orbit reduction.

### Count_q (modular counting)

`--problem count:n,q` — partition `[n]` into `q`-sized blocks. UNSAT
iff `q ∤ n`.

* Variables: `C(n, q)` — one per `q`-subset.
* Vertex axioms: `(∑_{S ∋ v} x_S) − 1 = 0`, one per vertex `v`.
* Over `𝔽_q`: degree-1 cert (theory: `q · ∑_S x_S − n = −n` in `𝔽_q`).
* Over `𝔽_p` with `p ≠ q`: degree grows with `n` (expected from PC lower
  bounds); see the README table for empirical cells.

When `p ≤ n` the orbit path fails because `p ∣ |S_n|`; add
`--alg-no-orbit` to use the dense engine.

### Tseitin (graph-based parity)

* `--problem tseitin-kn:N` — Tseitin on K_N, uniform charge 1. UNSAT
  iff `N` is odd.
* `--problem tseitin-cycle:N` — Tseitin on cycle C_N. UNSAT iff `N` odd.
* `--problem tseitin-petersen` — Tseitin on Petersen, uniform charge 1.
  `∑ c_v = 10` (even), so this is SAT; the correct answer is "no cert".
  Included as a soundness spot-check.

Tseitin is always run over `𝔽_2` (parity). Add `--alg-no-orbit` because
`2 ∣ |S_n|` for any `n ≥ 2`.

## Arbitrary CNF (no --problem flag)

If you have a DIMACS CNF with no recognized structural pattern, run the
algebraic probe directly:

```bash
./target/release/cascade --alg-preprocess 3 --alg-p 2 your.cnf
```

This uses the dense 𝔽₂ engine on the raw clauses. If a degree-3 cert
exists, UNSAT is reported immediately. Otherwise cascade falls through
to the CDCL pipeline (if not `--no-solve`).

This works but **does not exploit symmetry** — the orbit-reduced engine
needs a schema (variable → tuple) to run, and the raw CNF doesn't give
it one. Writing a schema for your problem is the main act of "using
cascade on a new family"; see the extension guide below.

## Reading the output

Three possible outcomes:

1. **`s UNSATISFIABLE`** + `cert at degree D` — a certificate was
   found. Always consider pairing with `--alg-cert` so the identity
   is saved to disk for the independent checker.
2. **`no cert at this (p, d)`** — the search completed without a cert.
   The solver prints three diagnostic hints: (a) try higher `d`,
   (b) try different `p` or `--alg-no-orbit`, (c) the instance may
   actually be SAT. The right next step depends on which.
3. **Timeout** — cascade doesn't have a built-in timeout for the
   algebraic probe; wrap it with shell `timeout N` if you need one.

## Choosing `(p, d)`

* For a PHP-shaped instance, start with `d = P` (the theoretical
  minimum over `𝔽_p` with `p ∤ P!`) and the smallest `p` with
  `p ∤ P! · H!`.
* For Count_q, try `p = q` first (cert always exists at `d = 1` when
  UNSAT), then vary `p` to produce the degree-vs-characteristic data.
* For Tseitin, `p = 2` is the interesting case; other primes need
  explicit Boolean axioms (not yet supported).
* If both are unknown, a safe first sweep is `d ∈ {1, 2, 3, 4, 5}` at
  `p ∈ {2, 3, 5, 7, 11}`. Most instances terminate in one of these
  cells or clearly blow up beyond them.

## Certificate format

Plain text, deliberately easy to parse. First few lines:

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
...
end
mult 0
term 4
...
end
```

* `p / d / n` — prime, degree, variable count.
* One `axiom <i> ... end` block per axiom (just the input axioms echoed
  into the cert for self-containment).
* One `mult <i> ... end` block per nonzero multiplier.
* Each `term <coef> <var_1> <var_2> ...` is a monomial.

The checker reads this and evaluates `∑ m_i · A_i`, confirming the
result reduces to the constant `1` modulo `p` and modulo the multilinear
identifications `x_i^2 = x_i`. Failure modes:

* **`s REJECTED sum does not reduce to 1`** — the cert is malformed or
  tampered. The checker will not accept it.
* **`parse error at line N`** — the cert is syntactically broken;
  check for editor-introduced whitespace or encoding issues.

## Extending cascade to a new problem family

Adding a new problem = a ~50 LOC factory in `src/problems.rs`:

```rust
pub fn my_family(arg1: u32, arg2: u32, prime: u8) -> (TupleVarSchema, Vec<PolyP>) {
    let schema = TupleVarSchema {
        bases: vec![BaseSet::new("X", arg1), BaseSet::new("Y", arg2)],
        tuple_kind: TupleKind::Ordered,        // or UnorderedPair / UnorderedSubset { size: k }
        group: GroupSpec::FullProduct,         // or Diagonal
    };
    let mut axioms = Vec::new();
    // ... build polynomial axioms over 𝔽_p ...
    (schema, axioms)
}
```

Plus three lines in `src/main.rs` to wire a CLI name. See `php_functional`,
`count_q_partition`, and `tseitin_graph` for concrete templates.

**Soundness requirement.** The axiom set must be closed under the group
action: for every generator `g` and axiom `A_i`, `g · A_i` must equal
some axiom `A_j`. The engine catches violations with a clear panic, but
it's easier to design the factory to be closed by construction
(uniform charges on symmetric graphs, symmetric axiom schemas).

## When to run the heavy cases

The end-to-end reproducer (`./scripts/reproduce.sh`) runs the ~5-minute
subset. The full picture requires a few slower runs:

| Instance | Expected time | Expected RAM |
|---|---|---|
| PHP_{7,6} d=7 | ~75 s | ~900 MB |
| PHP_{8,7} d=7 | ~10-30 min | ~5 GB |
| PHP_{8,7} d=8 | unknown; the current open frontier |

These are run individually with explicit CLI; they are not in the
default reproducer to keep its runtime sane.

## Further reading

* `README.md` — scope, architecture, published empirical tables.
* `src/algebra/ns_cert.rs` — cert format and the in-solver verifier
  (mirrors the standalone `cascade_cert_verify` logic).
* `src/tuple_schema.rs` — variable-tuple schema types, if you want to
  design a new family.
* `src/problems.rs` — working examples of problem factories.
