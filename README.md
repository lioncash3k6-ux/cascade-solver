# cascade

A research solver for structured combinatorial infeasibility problems,
written in Rust. Built around a shared engine that composes multiple
proof legs (resolution / CDCL, group-aware, algebraic / Nullstellensatz)
and produces externally-auditable certificates where possible.

This is a **research tool in active development**, not a validated
artifact. External interest is visible (clones from non-authors) but no
citations and no issues yet; treat results as reproducible within the
regimes we have measured, not as a general-purpose solver.

## Scope — what this tool is and is not

**Does well.** Combinatorial infeasibility problems with:

* Substantial group symmetry (so orbit reduction gives polynomial
  savings).
* Low Nullstellensatz / polynomial-calculus degree over *some* `𝔽_p`
  (so the algebraic leg terminates).
* Small enough variable count to fit the monomial space at the needed
  degree. Current envelope: up to `n = 56` vars at `d = 7` fits in
  ~5.5 GB RAM and ~14 min (PHP_{8,7}); larger instances and
  higher degrees scale roughly as `n_axioms · n_monos`.

**Does not do.**

* **Industrial SAT.** Kissat wins here; wrong regime for this tool.
* **Ramsey numbers.** NS degree is `Ω(n)` (confirmed from own data), so
  the algebraic leg cannot close Ramsey problems. Ramsey work in this
  repo uses the CDCL + symmetry legs only.
* **Proving P vs NP / breaking SAT.** The observed polynomial NS proofs
  of PHP etc. are in a *stronger proof system* than resolution, which is
  expected and well-known. The contribution is the specific combination
  of orbit reduction, characteristic variation, and independent cert
  verification, not the existence of the proofs themselves.

## Problem families (Stages 1–3, 2026-04-20)

Pigeonhole, Count_q, and Tseitin. Each has a CLI entrypoint that feeds
a generic orbit-reduced Nullstellensatz engine over `𝔽_p`. Every UNSAT
verdict emits a certificate that the independent `cascade_cert_verify`
binary re-checks without touching solver code.

```bash
cascade --alg-preprocess D --alg-p P --problem FAMILY[:args] input.cnf
```

### PHP (functional encoding)

All measurements on the current head (colex perfect-hash, commit
`a436daa`). `/usr/bin/time -v`, single 24-core Linux box, RSS peak
reported by the kernel.

| Instance | Setting | Time | Peak RAM | Verdict |
|---|---|---:|---:|---|
| PHP_{5,4} d=5 | 𝔽₇, orbit | 0.17 s | 10 MB | cert |
| PHP_{6,5} d=6 | 𝔽₇, orbit | 0.98 s | 35 MB | cert |
| PHP_{7,6} d=7 | 𝔽₁₁, orbit | 75 s | 886 MB | cert |
| PHP_{8,7} d=7 | 𝔽₁₁, orbit | 14 min | 5.5 GB | no cert (correct: `PHP_{P,P-1}` needs `d ≥ P`) |
| PHP_{8,7} d=8 | 𝔽₁₁, orbit | — | — | open frontier; estimated 20–40 GB and a few hours |

CLI: `--problem php:P,H`.

### Count_q (modular counting principle)

Partition `[n]` into q-sized blocks. UNSAT iff `q ∤ n`. Directly tests
characteristic sensitivity of NS.

Empirical `d_min` for a certificate (searched up to d = 5):

| q | n | `p = 2` | `p = 3` | `p = 5` | `p = 7` | `p = 11` | `p = 13` |
|---|---|---|---|---|---|---|---|
| 2 | 3 | **1** | 2 | 2 | 2 | 2 | 2 |
| 2 | 5 | **1** | > 5 | 4 | 4 | 4 | 4 |
| 2 | 7 | **1** | > 5 | > 5 | > 5 | > 5 | > 5 |
| 3 | 4 | > 5 | **1** | 2 | 2 | 2 | 2 |
| 3 | 5 | > 5 | **1** | > 5 | 4 | 4 | 4 |
| 3 | 7 | > 5 | **1** | > 5 | > 5 | > 5 | > 5 |

Bold = `p = q`. Theorem: summing all vertex axioms gives
`q · ∑_S x_S − n`, which reduces to `−n ≢ 0 mod q` when `q ∤ n`, giving
a degree-1 cert immediately. For `p ≠ q`, the degree grows with `n` as
expected from PC lower bounds.

CLI: `--problem count:n,q`. For `p ≤ n` the orbit reduction doesn't
apply (`p ∣ |S_n|`); use `--alg-no-orbit` for the dense engine.

### Tseitin (graph-based)

Vertex axioms `(∑_{e ∋ v} x_e) − c_v = 0` over `𝔽_p`. UNSAT over `𝔽_2`
when `∑_v c_v` is odd.

| Graph | Default | Verdict on uniform charge 1 |
|---|---|---|
| K_n | `tseitin-kn:n` | cert at d=1 over `𝔽_2` for `n` odd |
| C_n (cycle) | `tseitin-cycle:n` | cert at d=1 over `𝔽_2` for `n` odd |
| Petersen | `tseitin-petersen` | no cert (∑ c = 10 is even → SAT) |

Tseitin on K_n with charge 1 coincides mathematically with Count_2 on
K_n (same vertex-sum axiom). Kept separate to preserve the Tseitin
framing and to expose non-complete graphs (cycle, Petersen). The
infrastructure for custom automorphism groups (cycle → D_n, Petersen → S_5)
is wired (`find_orbit_cert_fp_with_gens`) but not yet used by the public
factories — `Aut(G) ⊊ S_n` reduction is follow-up work.

## SAT detection

For the structured families (PHP, Count_q, Tseitin), SAT / UNSAT is
determined by a closed-form condition the solver checks before
running the algebraic probe. When the instance is SAT, it emits a
DIMACS-standard model and exits 10, bypassing the UNSAT search
entirely.

| Family | SAT condition | Witness |
|---|---|---|
| `php:P,H` | `P ≤ H` | injection `pigeon i → hole i` |
| `count:n,q` | `q ∣ n` | natural partition `{1..q}, {q+1..2q}, ...` |
| `tseitin-*` | `∑_v c_v` even | Gaussian elim over 𝔽_2 on vertex-edge incidence |

```bash
cascade --alg-preprocess 1 --alg-p 2 --problem php:3,5 /tmp/dummy.cnf
# s SATISFIABLE
# v 1 -2 -3 -4 -5 -6 7 -8 -9 -10 -11 -12 13 -14 -15 0
```

When the SAT condition fails, cascade proceeds to the algebraic UNSAT
probe at the given `(p, d)`. The three possible end states for
`--problem` are now:

1. `s SATISFIABLE` + model (closed-form detector found a witness).
2. `s UNSATISFIABLE` + optional cert (algebraic probe closed).
3. `c [alg] no ... cert at degree D` (UNSAT cert not found at this
   `d`; the instance is still provably UNSAT by the closed-form
   condition, but the algebraic witness at this degree does not close).

## Certificates

Every `--alg-preprocess` UNSAT verdict produces a cert when
`--alg-cert <path>` is given. Format: plain-text
`p / d / n / axiom i / term c v₁ v₂ … / end / mult i / …`. Verified
by the independent `cascade_cert_verify` binary, which re-runs the
polynomial identity `∑ mᵢ · axiomᵢ ≡ 1` from scratch.

```bash
cascade --alg-preprocess 5 --alg-p 7 --problem php:5,4 \
        --alg-cert php_5_4.cert in.cnf
cascade_cert_verify php_5_4.cert    # independently re-checks the identity
```

Measured cert sizes: PHP_{5,4} d=5 — 52 KB; PHP_{6,5} d=6 — 1.0 MB;
verification < 1 s. Corrupting one coefficient rejects with
`s REJECTED sum does not reduce to 1`.

### VeriPB lowering (Gap 2)

For families with linear axioms (Count_q, Tseitin on regular graphs),
`--alg-cert-pb <stem>` additionally emits `<stem>.opb` (the formula
in OPB format) and `<stem>.pbp` (a VeriPB proof). These are accepted
by the stock [VeriPB](https://gitlab.com/MIAOresearch/software/VeriPB)
checker — no bespoke trust chain:

```bash
cascade --alg-no-orbit --alg-preprocess 1 --alg-p 3 --problem count:4,3 \
        --alg-cert-pb count43 /tmp/dummy.cnf
veripb count43.opb count43.pbp     # external: s VERIFIED UNSATISFIABLE
```

Verified cells (external `veripb 3.0.1`): `count:{4,3|5,3}` over 𝔽_3,
`count:{5,2|7,2}` over 𝔽_2. PHP and nonlinear-axiom families need a
richer lowering (expanding polynomial multipliers into PB
operations) and are follow-up work.

## Engineering story — PHP memory trajectory (2026-04-20)

Two data-structure decisions collapsed PHP from "needs a workstation"
to "runs on a laptop." The same instances, over a three-commit window:

| Instance | Original | Stage 1 (b34a51a) | Colex (a436daa) |
|---|---|---|---|
| PHP_{6,5} d=6, 𝔽₇ | 1.9 s / 166 MB | 1.7 s / 69 MB | **0.98 s / 35 MB** |
| PHP_{7,6} d=7, 𝔽₁₁ | 218 s / 4.47 GB | 260 s / 3.05 GB | **75 s / 886 MB** |
| PHP_{8,7} d=7, 𝔽₁₁ | timeout @ 1800 s, 40 GB | 60 min / 22.8 GB | **14 min / 5.5 GB** |

**Stage 1 — drop `mono_action`.** The per-generator monomial-image
table `Vec<Vec<u32>>` was `n_gens × n_monos × 4 B` — 14 GB at
PHP_{8,7} d=7 and the dominant memory cost. Dropping it and recomputing
images on-the-fly as `bits_index[apply_bits(monos_bits[mi],
&var_tables[gi])]` saved the memory at a modest time cost.

**Colex perfect hash — drop `bits_index`.** The remaining giant was
the `HashMap<u128, usize>` that mapped monomial bits to enumeration
index (~15–20 GB at PHP_{8,7} scale). Replaced by a direct
combinatorial ranking function (colex) that uses only a tiny
`(n+2)·(d+2)` binomial table — a few KB. Both the time and memory
improvements come from this step: no hash probe, no HashMap overhead,
O(d) arithmetic for each lookup.

Full derivation and measurements in
[`docs/ARCHITECTURE.md § 5`](docs/ARCHITECTURE.md#5-colex-perfect-hash-indexing).

Next natural move (not yet implemented): factored bit-swap
representation of adjacent-transposition generators on the u128
monomial — reclaims further time by turning `apply_bits` into a
single u128 XOR-mask swap for the structural case.

## End-to-end reproduction

```bash
cargo build --release
./scripts/reproduce.sh
```

Runs the full demonstration across:

* **PHP** — 5,4 through 7,6 (times from this machine: 0.17 s / 1 s /
  75 s, total ≈ 80 s).
* **Count_q** — a `(p, q)` grid across 𝔽_2, 𝔽_3, 𝔽_5, 𝔽_7, 𝔽_11, 𝔽_13
  (all sub-second at the sizes tested).
* **Tseitin** — K_5, K_6, C_5, C_7, Petersen.
* **Certificate round-trip** — emits a PHP_{6,5} d=6 cert (~1 MB) and
  re-verifies it via the independent `cascade_cert_verify` binary, then
  corrupts a coefficient and confirms the verifier rejects it.
* **VeriPB validation** — four Count_q cells lowered to
  `<stem>.opb + <stem>.pbp`, fed to the stock `veripb` binary, all
  return `s VERIFIED UNSATISFIABLE` (skipped if `veripb` is not on
  `PATH`).

Total runtime ≈ 1 min 20 s on a modern machine with ≥ 2 GB RAM
(measured 78.8 s on a 24-core box).

**Heavy cases** not run by default (invoke manually if curious):

```bash
./target/release/cascade --alg-preprocess 7 --alg-p 11 \
    --problem php:8,7 /tmp/dummy.cnf                       # ~14 min, 5.5 GB
./target/release/cascade --alg-preprocess 8 --alg-p 11 \
    --problem php:8,7 /tmp/dummy.cnf                       # open frontier
```

## Architecture

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for a comprehensive
walk-through of the solver internals: tuple-schema abstraction,
colex perfect-hash indexing, orbit engine phase breakdown, problem
factories, certificate formats, VeriPB lowering, extension points,
and soundness / trust-chain analysis. ~1150 lines with file:line
pointers into the source.

Short summary: legs on a shared propagator bus.

| Leg | Mechanism | Status |
|---|---|---|
| 1. Logical (CDCL) | CaDiCaL 2.2.1 + IPASIR-UP | inherited |
| 2. Statistical (VSIDS) | CaDiCaL | inherited |
| 3. Group-aware | Online symmetry propagator + `cb_decide` | shipped |
| 4. Algebraic | NS over `𝔽_p` (dense + orbit-reduced) | shipped |
| 5. Proof-native | VeriPB / DRAT composition + native NS cert + verifier | partial |
| 6. Stratified | 2-level cube-and-conquer | partial |

The `cb_decide` symmetry hook (~20 LOC in `src/symmetry/online.rs`) is
the largest group-aware empirical win; see the Ramsey table below.

## Ramsey (CDCL + symmetry legs only)

| Instance | v0.5 | v0.6 best | Δ | Setting |
|---|---:|---:|---|---|
| R(3,3) / K_6 | 1 | 0 | ✓ | any |
| R(3,5) / K_14 | 32 | 3 | −91 % | `CASCADE_SYM_DECIDE=50` |
| R(3,6) / K_18 | 1,734 | 1,024 | −41 % | `CASCADE_SYM_DECIDE=full` |
| R(4,4) / K_17 SAT | 1,700 | 270 | −84 % | `CASCADE_SYM_DECIDE=20` |
| R(4,5) / K_25 | 0 | 0 | = | any (certified) |

All verified end-to-end (satsuma equisat + CaDiCaL DRAT). No algebraic
leg involvement — NS degree is `Ω(n)` for Ramsey so the algebraic path
is not a fit.

## Layout

```
src/
  cadical.rs              CaDiCaL 2.2.1 + IPASIR-UP
  symmetry/
    online.rs             online symmetry propagator + cb_decide
    schreier_sims.rs      Schreier-Sims stabilizer chain
  propagator/composite.rs multi-propagator bus
  tuple_schema.rs         generic variable-tuple schema + group action
                          (Ordered / UnorderedPair / UnorderedSubset{k})
  problems.rs             problem-family factories:
                            php_functional, ramsey_disjunctive,
                            count_q_partition,
                            tseitin_graph / tseitin_kn /
                            tseitin_cycle / tseitin_petersen
  algebra/
    poly.rs               multilinear polynomials over 𝔽₂
    ns.rs                 naive NS over 𝔽₂
    ns_fp.rs              dense NS over 𝔽_p
    orbit_ns.rs           generic orbit-reduced NS + ColexIndex
    php_orbit.rs          PHP-specific engine (regression baseline)
    ns_cert.rs            serializable cert format + in-solver verifier
    ns_to_pb.rs           VeriPB lowering for linear-axiom families
  bin/cascade_cert_verify.rs   standalone cert verifier
scripts/
  reproduce.sh            end-to-end demonstration runner
docs/
  ARCHITECTURE.md         comprehensive internals walk-through
  TUTORIAL.md             hands-on CNF → verified cert walkthrough
```

## Build & test

```bash
cargo build --release
cargo test --release      # 180 tests, ~2 min
```

## Honest limitations

* **Orbit reduction requires `p ∤ |G|`.** For Count_q with `p = q ≤ n`,
  the orbit path is unusable; we fall back to the dense engine, which
  runs out at roughly `n = 7, d = 5`.
* **Pair BFS + matrix scatter is the hot path at PHP_{8,7} d=7 scale**
  (about 640 s on its own, ~77 % of wall time). Factored bit-swap
  generators would reduce each `apply_bits` call from O(d) to O(1),
  the natural next speedup.
* **PHP_{10,9}** needs `d = 10` on 90 vars, `∑_{k ≤ 10} C(90, k) ≈ 10¹²`
  monomials — beyond anything we can enumerate. Direct orbit enumeration
  without per-monomial materialization is genuine research work.
* **VeriPB lowering is linear-axiom only.** Count_q and Tseitin (on
  regular graphs with uniform charge) lower cleanly; PHP's quadratic
  AMO axioms need a richer proof structure, not yet implemented.
* **Tseitin custom-Aut reduction** (cycle, hypercube, Petersen) is wired
  (`find_orbit_cert_fp_with_gens`) but the public factories still default
  to `S_n`, which works only for K_n.
* **No formal complexity claims** beyond reporting measured degrees and
  times. Expressions like "polynomial" or "exponential" in the text
  refer to well-known proof-complexity facts about the underlying
  principles, not new results from this tool.

## License

MIT.
