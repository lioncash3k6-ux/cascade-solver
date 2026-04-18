# cascade

A structural SAT solver for Ramsey-like combinatorial formulas, written in Rust.
Built around the thesis that **group-aware + algebraic + CDCL composed on one
bus** beats any single technique on structured instances.

## Headline results

### Ramsey (certified end-to-end)

| Instance | v0.5 | v0.6 best | Δ | Setting |
|---|---:|---:|---|---|
| R(3,3)/K_6 | 1 | 0 | ✓ | any |
| R(3,5)/K_14 | 32 | **3** | **−91%** | `CASCADE_SYM_DECIDE=50` |
| R(3,6)/K_18 | 1,734 | **1,024** | **−41%** | `CASCADE_SYM_DECIDE=full` |
| R(4,4)/K_17 SAT | 1,700 | **270** | **−84%** | `CASCADE_SYM_DECIDE=20` |
| R(4,4)/K_18 | 17 | 141 | — | default |
| R(4,5)/K_25 | 0 | 0 | = | any |

All verified end-to-end (satsuma equisat + cadical DRAT). Every UNSAT verdict
checked by veripb + drat-trim.

### Competition benchmark (2025 SAT unknowns, 50 smallest, 5s)

- **cascade 18 solved, Kissat 12 solved.**
- **6 unique cascade wins, 0 unique Kissat wins.**

### Pigeonhole (algebraic engine)

Functional-encoding + orbit-reduced NS over 𝔽_p, driven by a generic
`(TupleVarSchema, axioms)` engine shared with Ramsey:

| Instance | 𝔽₂ / CNF (dense) | 𝔽_p / functional (orbit) |
|---|---|---|
| PHP_{5,4} | **OOM** at d=5 | d=5, **0.17s** (𝔽₇) |
| PHP_{6,5} | OOM | d=6, **1.9s** (𝔽₇) |
| PHP_{7,6} | OOM | d=7, **238s** (𝔽₁₁) |

Key facts:

* **Encoding matters.** The classical "PHP has low NS degree" result is for
  *functional* encoding (`∑_h x(p,h) − 1 = 0`), not the disjunctive CNF. Switching
  encodings unlocked PHP_{5,4}.
* **Prime matters.** When `p ∤ |G| = P!·H!`, G-invariant certs exist.
  When `p | |G|` (e.g., 𝔽₃ on PHP_{5,4} since 3 | 5!), certs exist but are
  non-invariant and orbit reduction fails by returning "no cert".
* **Engine optimization: 10× across the board.** Three-layer rewrite —
  index-key pair BFS (`Vec<u32>` replaces `BTreeMap<(usize, Monomial), ...>`),
  unified per-generator monomial-index action tables, and u128 bitmask
  monomial representation with bit-OR product / popcount degree. PHP_{6,5}
  d=6 went from 22s → 1.9s; PHP_{7,6} d=7 moved from OOM-at-600s to a 238s
  certified UNSAT.

## GAPS architecture

Five proof techniques compose on a single IPASIR-UP bus:

| Leg | Mechanism | Status |
|---|---|---|
| 1. Logical (CDCL) | CaDiCaL 2.2.1 | ✓ inherited |
| 2. Statistical (VSIDS) | CaDiCaL | ✓ inherited |
| 3. **G**roup-aware | Online symmetry propagator + cb_decide | ✓ shipped (v0.6) |
| 4. **A**lgebraically-lifted | NS-lite over 𝔽_p (CNF and functional encoding) | ✓ wired |
| 5. **P**roof-native | Post-hoc VeriPB + DRAT composition | partial |
| 6. **S**tratified | 2-level cube-and-conquer | partial |

The biggest empirical win this release: **`cb_decide`** (~20 lines) tells
CaDiCaL where to branch based on the lex-leader ordering. Settling the first N
canonical positions before letting VSIDS take over drops R(4,4)/K_17 from 1,700
to 270 conflicts.

## Controls

```bash
# Symmetry-aware decision guidance (empirical sweet spot: 20 for SAT, full for UNSAT)
CASCADE_SYM_DECIDE=20 cascade input.cnf

# Algebraic preprocessing: degree-D Nullstellensatz-lite over 𝔽_p
cascade --alg-preprocess 2 input.cnf                                  # 𝔽₂, CNF
cascade --alg-preprocess 4 --alg-p 5 input.cnf                        # 𝔽₅, CNF
cascade --alg-preprocess 5 --alg-p 7  --problem php:5,4    in.cnf     # generic orbit-reduced 𝔽_p
cascade --alg-preprocess 7 --alg-p 11 --problem php:7,6    in.cnf     # PHP_{7,6}, ~4min
cascade --alg-preprocess 3 --alg-p 7  --problem ramsey:3,3,6 in.cnf   # Ramsey smoke test

# Algebraic side-channel on the propagator bus
cascade --alg-propagate input.cnf
```

## Research findings (definitive, from v0.6 + session work)

1. **Orbit closure of blocking clauses over 𝔽₂: fundamentally unsound.**
   `h(C)` can block the canonical representative. Confirmed with both naive
   and conjugation approaches.

2. **Orbit closure of CDCL-learned clauses: sound but redundant.** Symmetry
   propagator already prevents non-canonical search; orbit images add no
   new pruning.

3. **cb_decide is the dominant group-aware technique.** 20 lines outperform
   all other symmetry innovations combined.

4. **PHP encoding matters more than symmetry reduction.** The "PHP has low NS
   degree" result is for the *functional* encoding (linear totality
   `∑_h x(p,h) − 1 = 0`), not the disjunctive CNF encoding. Switching
   encodings drops the degree from Θ(n) over 𝔽₂ to O(log n) over 𝔽_p (p ∤ P).

5. **G-invariant NS over 𝔽₂ for PHP is a dead end.** |G| = P!·H! is even, so
   symmetrization gives the zero certificate. Documented in
   `src/algebra/php_orbit.rs` as a negative result. The way forward is
   orbit-reduced NS over 𝔽_p with p ∤ |G| — where invariant certs exist.

## Layout

```
src/
  cadical.rs              in-process CaDiCaL 2.2.1 + IPASIR-UP
  symmetry/
    online.rs             online symmetry propagator (+ cb_decide)
    schreier_sims.rs      Schreier-Sims stabilizer chain
  propagator/
    composite.rs          multi-propagator bus
  tuple_schema.rs         generic variable-tuple schema + group action
  problems.rs             problem-family factories (PHP, Ramsey, …)
  algebra/                GAPS leg 4
    poly.rs               multilinear polynomials over 𝔽₂
    ns.rs                 naive NS over 𝔽₂, bit-packed matrix
    ns_fp.rs              NS over 𝔽_p (odd prime), functional axioms
    orbit_ns.rs           generic orbit-reduced NS engine, u128 bitmask fast path
    php_orbit.rs          PHP-specific orbit engine (regression baseline)
    tseitin.rs            clause encoding of NS certificates
    propagator.rs         algebraic side-channel propagator
  bcp.rs                  two-watched-literals BCP cascade
  cardinality.rs          Sinz-2005 + Ramsey degree bounds
  biclique.rs             K4/K5 biclique group propagation
  ...
```

## Build & test

```bash
cargo build --release
cargo test --release
```

Requires `cadical`, `satsuma`, `veripb`, `drat-trim` on PATH for `--certified`
mode. Without them, cascade still parses and runs BCP + CDCL.

## Run

```bash
cascade <input.cnf> [--proof out.drat] [--equisat-proof out.pbp]
                    [--timeout SECS] [--certified]
                    [--no-solve] [--no-symmetry] [--no-card] [--no-bcp]
                    [--alg-preprocess D] [--alg-propagate]
```

## License

MIT.
