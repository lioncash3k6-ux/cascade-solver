# cascade

**Work in progress.** A structural-cascade SAT solver written in Rust, built around
the idea that proof-producing preprocessing can collapse hard-looking instances
to something unit propagation alone can close.

The architecture is a four-layer pipeline: a typed constraint IR on top, an
augmentation IR carrying per-clause justifications, a BCP/search engine, and an
external verifier at the bottom. Everything a stage emits is meant to be a
step in a verifiable proof.

## Status

Weeks 1–5 landed. What currently works end-to-end:

- **Parse** — streaming DIMACS CNF reader.
- **Constraint IR** — `Clause`, `Cardinality`, `Xor`, `AtMostOne`, `Symmetry`, `Definition`.
- **Augmentation IR** — `Augmentation { id, clause, justification }` with `Input` / `Rup` /
  `Rat` / `Sr` / `Pr` / `Propagator` / `Delete`.
- **Proof writer** — DRAT / LRAT / DSR stubs (skips axioms; emits derived clauses).
- **CaDiCaL backend** — subprocess wrapper, DRAT body proofs, model parsing.
- **Satsuma stage** — invokes `satsuma` for orbitopal symmetry breaking and
  patches up its VeriPB footer so `veripb` can verify the equisat proof.
- **Cardinality stage** — Sinz-2005 sequential-counter at-most-k encoding, plus
  a Ramsey auto-detector that reads `(s, t)` and `n` from the CNF and adds
  link-graph degree bounds `red_deg ≤ R(s−1,t) − 1`, `blue_deg ≤ R(s,t−1) − 1`.
- **BCP cascade** — linear-scan unit propagation to fixpoint. If the
  augmented formula collapses under BCP, we skip CDCL entirely and emit a
  trivial body proof.

### Headline result

`R(4,5) / K_25` on a published augmented CNF (600 vars, 66 679 clauses):

```
c [bcp] UNSAT after 134 propagations (0.007s)
s UNSATISFIABLE

$ drat-trim ... proof.drat
c UNSAT via unit propagation on the input instance
s VERIFIED
```

End-to-end soundness has been checked on R(4,4)/K_18: satsuma equisat proof
verified by `veripb`, body proof verified by `drat-trim`.

## Known gaps

- The cardinality stage adds degree-bound clauses as **axioms**. Their
  soundness as theorems of the bare CNF (link-graph argument) is not yet
  emitted as a verifiable proof step — same gap as the manual 3-file proofs
  this project is trying to close.
- No chain-binary generator yet; no cube-and-conquer (Stage 3); no 2WL BCP;
  no codegree encoding. All on the roadmap.
- The bundled DRAT proof emitter only handles the trivial-BCP case. Non-BCP
  UNSAT still goes out through CaDiCaL.

## Layout

```
src/
  lib.rs            module exports
  types.rs          Var / Lit / ClauseId / Clause
  dimacs.rs         streaming CNF parser
  constraint.rs     Layer 1: typed constraint IR
  augmentation.rs   Layer 2: (clause, justification) log
  proof.rs          DRAT / LRAT / DSR writer
  backend/
    mod.rs          Backend trait
    cadical.rs      CaDiCaL subprocess
  symmetry/
    mod.rs          SymmetryBreaker trait
    satsuma.rs      satsuma wrapper + VeriPB footer fixup
  cardinality.rs    Sinz-2005 + Ramsey degree bounds
  bcp.rs            Stage 2 cascade engine
  main.rs           CLI pipeline
```

## Build

```
cargo build --release
cargo test
```

## Run

```
cascade <input.cnf> [--proof out.drat] [--equisat-proof out.pbp]
                    [--timeout SECS]
                    [--no-solve] [--no-symmetry] [--no-card] [--no-bcp]
```

The two-file proof (`--equisat-proof` + `--proof`) together attests that the
bare input CNF is UNSAT.

## License

MIT.
