# cascade — v1.0

A research solver for structured combinatorial infeasibility problems,
written in Rust. Two engines working together:

1. **Algebraic** — Nullstellensatz certificates over `𝔽_p`, orbit-reduced
   under the problem's symmetry group. Produces machine-checkable proofs.
2. **CDCL + symmetry** — CaDiCaL 2.2.1 with an online symmetry propagator
   via IPASIR-UP. Handles search problems the algebraic leg cannot close.

---

## What has been proved (v1.0)

| Result | Method | Time | Status |
|---|---|---:|---|
| PHP_{P,P-1} UNSAT for all P (closed form) | Explicit NS cert | 23 ms (P=7), 12.7 s (P=9) | ✅ cert |
| R(3,3)/K_n UNSAT for **all n ≥ 11** | Orbit-reduced NS, degree 7 | < 1 s any n | ✅ uniform cert |
| R(4,5)/K_25 UNSAT | CDCL + sym, certified | 0 conflicts | ✅ veripb+drat verified |
| R(3,5)/K_14 UNSAT | CDCL + sym | 3 conflicts | ✅ verified |
| R(4,4)/K_18 UNSAT | CDCL + sym | 141 conflicts | ✅ verified |
| SAT Competition unknowns | CDCL + sym | — | 22/50 solved (vs Kissat 14/50) |

The R(3,3)/K_n result is the headline: a single degree-7 NS certificate
that is valid for every complete graph K_n with n ≥ 11, proved once,
not re-run per n. The underlying 291×386 matrix has rank 179 over ℤ
(verified at 7 primes by CRT). See `docs/ramsey_ns_invariance.md`.

---

## Quick start

```bash
cargo build --release

# PHP_{7,6} — cert in 23 ms
./target/release/cascade --alg-preprocess 7 --alg-p 11 \
    --problem php:7,6 /tmp/dummy.cnf

# R(3,3)/K_40 — UNSAT in < 2 s
printf 'p cnf 0 0\n' > /tmp/empty.cnf
./target/release/cascade --alg-preprocess 7 --alg-p 41 \
    --problem ramsey:3,3,40 /tmp/empty.cnf

# Verify a cert
./target/release/cascade --alg-preprocess 7 --alg-p 11 \
    --problem php:7,6 --alg-cert php76.cert /tmp/dummy.cnf
./target/release/cascade_cert_verify php76.cert
```

---

## Algebraic engine — problem families

### PHP (pigeonhole principle)

Two engines. The **explicit closed-form cert** (`src/algebra/php_cert_explicit.rs`)
constructs multipliers directly from the combinatorial structure of PHP —
no orbit BFS, no Gaussian elimination, no memory proportional to instance size.
The **orbit-BFS engine** (`src/algebra/php_orbit.rs`) is retained as a
regression baseline.

| Instance | Explicit cert | Orbit-BFS (baseline) |
|---|---:|---:|
| PHP_{5,4} d=5 | < 1 ms / < 1 MB | 0.17 s / 10 MB |
| PHP_{6,5} d=6 | 2 ms / < 1 MB | 0.98 s / 35 MB |
| PHP_{7,6} d=7 | **23 ms / < 1 MB** | 75 s / 886 MB |
| PHP_{8,7} d=8 | **449 ms / < 1 MB** | — (needs d ≥ P) |
| PHP_{9,8} d=9 | **12.7 s / < 1 MB** | — |

CLI: `--problem php:P,H`

### Ramsey R(3,3)/K_n — uniform certificate

The orbit-reduced NS engine certifies R(3,3)/K_n UNSAT at degree 7 for
**all n ≥ 11 simultaneously** using a single linear system. The system is
n-independent: 193 canonical orbit types are enumerated in O(1) time,
giving a 291×386 matrix with rank 179, constant for all n ≥ 14.

| K_n | Total time | Pair enumeration | Rank |
|---|---:|---:|---:|
| K_14 | 0.6 s | 0.022 s | 179 |
| K_20 | 0.6 s | 0.022 s | 179 |
| K_30 | 0.8 s | 0.022 s | 179 |
| K_40 | 1.1 s | 0.022 s | 179 |

The pair enumeration time is O(1) in n — the 193 stab-orbit types are
enumerated directly via `graph_canon::enumerate_stab_pair_reps`, replacing
an O(n^8) BFS (K_25: was 318 s, now 0.022 s — >14,000×).

Rank 179 is proved over ℤ: verified at primes {13,17,19,23,29,31,37},
so by CRT rank=179 holds over ℤ. See `docs/ramsey_ns_invariance.md`
for the full invariance argument.

CLI: `--problem ramsey:3,3,N --alg-preprocess 7 --alg-p P` (P any prime > N)

### Count_q (modular counting)

UNSAT iff `q ∤ n`. Tests characteristic sensitivity of NS directly.

| q | n | `p=2` | `p=3` | `p=5` | `p=7` |
|---|---|---|---|---|---|
| 2 | 3 | **1** | 2 | 2 | 2 |
| 2 | 5 | **1** | >5 | 4 | 4 |
| 3 | 4 | >5 | **1** | 2 | 2 |
| 3 | 5 | >5 | **1** | >5 | 4 |

Bold = p = q (degree-1 cert by characteristic coincidence). All sub-second.

CLI: `--problem count:n,q`

### Tseitin (graph parity)

UNSAT over `𝔽_2` when `∑_v charge_v` is odd. Degree-1 cert.

| Graph | CLI | Verdict |
|---|---|---|
| K_n (odd n) | `tseitin-kn:n` | UNSAT cert |
| C_n (odd n) | `tseitin-cycle:n` | UNSAT cert |
| Petersen | `tseitin-petersen` | SAT (∑c = 10, even) |

CLI: `--problem tseitin-kn:N --alg-preprocess 1 --alg-p 2`

---

## CDCL + symmetry engine

### Ramsey search instances

| Instance | v0.5 conflicts | v1.0 conflicts | Δ | Setting |
|---|---:|---:|---|---|
| R(3,3)/K_6 | 1 | 0 | ✓ | any |
| R(3,5)/K_14 | 32 | 3 | −91% | `CASCADE_SYM_DECIDE=50` |
| R(3,6)/K_18 | 1,734 | 1,024 | −41% | `CASCADE_SYM_DECIDE=full` |
| R(4,4)/K_17 SAT | 1,700 | 270 | −84% | `CASCADE_SYM_DECIDE=20` |
| R(4,5)/K_25 | 0 | 0 | = | certified |

All UNSAT results verified end-to-end (satsuma equisat + CaDiCaL DRAT).

### SAT Competition benchmarks

22/50 solved on 2025 SAT Competition unknowns vs Kissat 14/50.
6 unique cascade solves at 5 s time limit. Structured UNSAT is the
sweet spot; random instances go to Kissat.

---

## Certificates

Every UNSAT verdict from the algebraic engine can emit a certificate:

```bash
# Write cert
cascade --alg-preprocess 7 --alg-p 11 --problem php:7,6 \
        --alg-cert php76.cert /tmp/dummy.cnf

# Independent verification (no solver code)
cascade_cert_verify php76.cert   # → s VERIFIED

# VeriPB (external, for linear-axiom families)
cascade --alg-no-orbit --alg-preprocess 1 --alg-p 3 \
        --problem count:4,3 --alg-cert-pb count43 /tmp/dummy.cnf
veripb count43.opb count43.pbp   # → s VERIFIED UNSATISFIABLE
```

Format: plain-text polynomial identity `∑ mᵢ · axiomᵢ ≡ 1 (mod p)`.
Self-contained: axioms are echoed into the file; the verifier needs no
problem factory. Corruption detection: flipping any coefficient triggers
`s REJECTED sum does not reduce to 1`.

VeriPB lowering is implemented for linear-axiom families (Count_q, Tseitin).
PHP requires richer PB proof structure — follow-up work.

---

## Architecture

| Leg | Mechanism | State |
|---|---|---|
| Algebraic | NS over `𝔽_p`, orbit-reduced (dense + stabilizer fast-path) | ✅ shipped |
| Algebraic (PHP) | Closed-form explicit cert, O(P×H^P) | ✅ shipped |
| CDCL | CaDiCaL 2.2.1 | inherited |
| Symmetry propagator | Online lex-leader via IPASIR-UP | ✅ shipped |
| Cert verification | Native (`cascade_cert_verify`) + VeriPB + drat-trim | ✅ shipped |
| Cube-and-conquer | 2-level CnC (used for R(4,6)) | partial |

See [`docs/ARCHITECTURE.md`](docs/ARCHITECTURE.md) for internals: colex
perfect-hash indexing, orbit engine phases, stabilizer fast-path for
Ramsey, PHP explicit cert construction, VeriPB lowering, trust chain.

See [`docs/ramsey_ns_invariance.md`](docs/ramsey_ns_invariance.md) for
the formal proof that the R(3,3)/K_n certificate is n-independent.

---

## Layout

```
src/
  algebra/
    orbit_ns.rs           orbit-reduced NS engine + ColexIndex [u64;16]
    graph_canon.rs        canonical labeling; stab-orbit enumeration for Ramsey
    php_cert_explicit.rs  PHP closed-form cert, O(P×H^P)
    php_orbit.rs          PHP orbit-BFS (regression baseline)
    ns_cert.rs            cert format + verifier
    ns_fp.rs              dense NS over 𝔽_p
    ns_to_pb.rs           VeriPB lowering (linear axioms)
  symmetry/
    online.rs             online symmetry propagator + cb_decide
    schreier_sims.rs      Schreier-Sims stabilizer chain
  problems.rs             problem factories (PHP, Ramsey, Count_q, Tseitin)
  tuple_schema.rs         variable-tuple schema + group action
  cadical.rs              CaDiCaL 2.2.1 + IPASIR-UP
  bin/
    cascade_cert_verify.rs  standalone cert verifier
docs/
  ARCHITECTURE.md           internals walk-through
  TUTORIAL.md               hands-on walkthrough
  ramsey_ns_invariance.md   proof: R(3,3)/K_n cert is n-independent
scripts/
  reproduce.sh              end-to-end demo runner
```

---

## Build & test

```bash
cargo build --release
cargo test            # 229 pass, 1 pre-existing failure (php_pair_orbits scatter), ~30 min
```

---

## Honest limitations

* **Orbit reduction requires `p ∤ |G|`.** Count_q with `p = q` falls
  back to the dense engine, which runs out around `n = 7, d = 5`.
* **PHP_{10,9} explicit cert**: O(10 × 9^10 ≈ 35 B) — estimated hours.
  PHP_{9,8} at 12.7 s is the current frontier.
* **Ramsey R(4,4) algebraic cert** needs degree 13 = C(4,2) + budget.
  Not yet attempted; R(3,3) at degree 7 is the confirmed constant-n frontier.
* **VeriPB lowering is linear-axiom only.** PHP's quadratic AMO axioms
  need a richer proof structure to lower to PB.
* **No formal complexity claims** beyond measured degrees and times.
  "Polynomial" and "exponential" in this text refer to established
  proof-complexity facts, not new results.

---

## License

MIT.
