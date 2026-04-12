# cascade

A structural-cascade SAT solver written in Rust, built around the idea that
proof-producing preprocessing can collapse hard-looking instances to something
unit propagation alone can close.

Pipeline: parse → satsuma symmetry breaking → cardinality degree bounds →
2WL BCP cascade → CaDiCaL fallthrough. Every verdict can be independently
verified by external tools under `--certified` mode.

## Results

**48 / 100** instances solved on the SAT Competition 2025 unknown track
(30s timeout, single core). **Zero wrong answers.** Every SAT model verified
clause-by-clause against the original CNF. Every UNSAT verified by
veripb + drat-trim.

Highlights:
- R(4,4)/K_18 UNSAT in **0.05s** (0.52s certified) — originally required
  ~30 min on a cluster (Heule et al. 2017)
- R(4,5)/K_25 published augmented CNF: BCP-UNSAT in **3 ms**, drat-trim verified
- cliquecolouring, arles threshold, Ramsey instances: instant UNSAT via
  satsuma symmetry breaking

## Certified mode

```
cascade input.cnf --certified
```

Under `--certified`, **no cascade code is trusted**. Every verdict is
independently machine-checked:

- **UNSAT**: `veripb` verifies satsuma's equisat proof, `drat-trim` verifies
  CaDiCaL's body proof. Two independent tools confirm the bare CNF is UNSAT.
- **SAT**: model checked clause-by-clause against the **original** CNF (not the
  augmented one). Catches any augmentation or parsing bug.
- **Cardinality**: skipped under `--certified`. The degree-bound clauses are
  theorems of the bare Ramsey CNF (link-graph argument) but require
  exponential-length resolution proofs — beyond DRAT's practical reach.
  Available without `--certified` for a 10x speedup on Ramsey instances.

## Layout

```
src/
  lib.rs            module exports
  types.rs          Var / Lit / ClauseId / Clause
  dimacs.rs         streaming CNF parser
  constraint.rs     Layer 1: typed constraint IR
  augmentation.rs   Layer 2: (clause, justification) log
  proof.rs          DRAT / LRAT / DSR writer
  certify.rs        external verifier invocation (veripb, drat-trim, model check)
  backend/
    mod.rs          Backend trait
    cadical.rs      CaDiCaL subprocess (text DRAT for proof combining)
  symmetry/
    mod.rs          SymmetryBreaker trait
    satsuma.rs      satsuma wrapper + VeriPB footer fixup
  cardinality.rs    Sinz-2005 + Ramsey degree bounds
  bcp.rs            Stage 2: two-watched-literals BCP cascade
  main.rs           CLI pipeline
```

## Build

```
cargo build --release
cargo test
```

Requires `cadical`, `satsuma`, `veripb`, and `drat-trim` on PATH for full
functionality. Without them, cascade still parses and runs BCP.

## Run

```
cascade <input.cnf> [--proof out.drat] [--equisat-proof out.pbp]
                    [--timeout SECS] [--certified]
                    [--no-solve] [--no-symmetry] [--no-card] [--no-bcp]
```

## License

MIT.
