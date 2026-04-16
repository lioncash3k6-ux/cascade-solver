# Cascade v0.6 — Status

## Headline

**Online symmetry propagator live inside CaDiCaL via IPASIR-UP.** All 9
Ramsey benchmarks verify end-to-end with the propagator active under
`--certified`, including R(4,5)/K_25. Pure-online mode beats v0.5 on
3 of 5 benchmarks; certified mode wins on R(3,5)/K_14 (22 vs 32
conflicts) and R(4,4)/K_17 (1,611 vs 1,700).

## Certified Suite (9/9 VERIFIED, propagator active)

| Instance      | Verdict | Conflicts (v0.6) | Verifiers |
|---------------|---------|-----------------:|-----------|
| R(3,3)/K_5    | SAT     | 1                | veripb + model |
| R(3,3)/K_6    | UNSAT   | 0                | veripb + drat-trim |
| R(3,4)/K_8    | SAT     | 10               | veripb + veripb-card + model |
| R(3,4)/K_9    | UNSAT   | 0 body           | veripb + veripb-card + dsr-trim + drat-trim |
| R(3,5)/K_14   | UNSAT   | **22**           | veripb + veripb-card + drat-trim |
| R(3,6)/K_18   | UNSAT   | 1,818            | veripb + drat-trim |
| R(4,4)/K_17   | SAT     | **1,611**        | veripb + veripb-card + model |
| R(4,4)/K_18   | UNSAT   | 141              | veripb + veripb-card + drat-trim |
| R(4,5)/K_25   | UNSAT   | 0 body           | veripb + veripb-card + dsr-trim + drat-trim |

## Architecture — online symmetry layer (new in v0.6)

1. **Generator extraction** (`src/symmetry/generators.rs`) — parses
   satsuma's VeriPB proof for automorphism generators and the
   load-order used as lex baseline.
2. **LexComparator** (`src/symmetry/lex.rs`) — one per generator;
   O(amortized 1) frontier advance, snapshot stack for O(1) backjump,
   `StepOutcome::{Stalled,Satisfied,Violated,Propagate(lit)}`.
3. **SymmetryPropagator** (`src/symmetry/online.rs`) — owns the
   comparators, mirrors the trail, emits both-sides blocking clauses
   and proactive propagation with correct reason clauses.
4. **CompositePropagator** (`src/propagator/composite.rs`) — round-
   robin router so CaDiCaL's single external-propagator slot can
   host biclique + sym simultaneously.
5. **VeriPB red witness emission** (`src/symmetry/proof.rs`) — logs
   each blocking/propagation clause with its witnessing generator;
   post-solve composes a VeriPB proof using satsuma's def_order/
   load_order preamble.
6. **CNF merge** (`certify::merge_cnf_with_clauses`) — folds emitted
   sym clauses into the CNF drat-trim verifies against, so the body
   proof's RUP checks succeed.

## Verification chain

```
bare.cnf
  → [veripb]     satsuma equisat proof
  → [veripb]     card degree bounds (cutting-planes)
  → [veripb]     online-sym audit trail (red witnesses)  ← NEW in v0.6
  → [card]       Sinz sequential counter encoding
  → [dsr-trim]   chain DSR proof (odd n only)
  → [BCP]        warmstart propagation
  → [CaDiCaL]    CDCL body proof (DRAT) with sym propagator active
  → [drat-trim]  verify body proof against augmented CNF (including
                 online-sym clauses as axioms)
  → VERIFIED
```

## Non-certified fast mode

`--biclique --online-sym`: propagator active, satsuma SBP stripped
from CNF, `CASCADE_SYM_MAX_GENS=20` default cap.

| Instance      | Verdict | v0.5 | v0.6 | Δ |
|---------------|---------|-----:|-----:|---|
| R(3,3)/K_6    | UNSAT   | 1    | 0    | ✓ |
| R(3,5)/K_14   | UNSAT   | 32   | 22   | **-31%** |
| R(3,6)/K_18   | UNSAT   | 1,734| 1,818| +5% |
| R(4,4)/K_18   | UNSAT   | 17   | 141  | — (CNF-structure; not propagator) |
| R(4,4)/K_17   | SAT    | 1,700| 1,611| **-5%** |
| R(4,5)/K_25   | UNSAT  | 0    | 0    | trivial |

R(4,4)/K_18's 17 → 141 conflict count is NOT a propagator regression
— diagnostic with sym fully inert shows 141 conflicts too. The
difference is that pure-online mode removes satsuma's SBP clauses
from the CNF, and CaDiCaL's BCP-through-SBP was doing the work that
gave v0.5 its 17-conflict path on that instance.

## Key design decisions

1. **MIN lex convention** (canonical = lex-smallest). Matches
   satsuma's dom-line semantics `val(map) ≥ val(orig)`.
2. **Both-sides blocking clauses**: soundness requires negating v-side
   AND g(v)-side at each non-fixed-point prefix position.
3. **Proactive propagation enabled**: `Propagate(lit)` paths emit
   correct both-sides reason clauses.
4. **Default generator cap** at 20; `CASCADE_SYM_MAX_GENS` overrides.
5. **Pure-online replace mode** default. `CASCADE_ONLINE_SYM_OVERLAY=1`
   exposes overlay as a diagnostic (known-unsound; see below).

## Findings worth publishing

**Satsuma's SBP is not strict per-generator lex-leader.** Empirical
observation: satsuma's own SAT model for R(4,4)/K_17 has mixed
per-generator lex relations — some generators yield `orig > image`,
others `orig < image`, under satsuma's own generators. This is
impossible under any strict per-generator lex-leader convention (MIN
or MAX). Satsuma's SBP appears to be Schreier-Sims-flavored.

Consequence: layering our strict per-gen propagator on top of
satsuma's SBP (overlay mode) rejects satsuma's canonical models.
Overlay is fundamentally broken until our propagator's canonicality
matches satsuma's (Schreier-Sims selection, future work).

## Environment variables

- `CASCADE_SYM_MAX_GENS=<n>` — cap generators (default 20)
- `CASCADE_SYM_NO_PROPAGATE=1` — violations only
- `CASCADE_SYM_NO_VIOLATIONS=1` — propagations only
- `CASCADE_SYM_STATS=1` — dump per-gen stats on Drop
- `CASCADE_ONLINE_SYM_OVERLAY=1` — force overlay (diagnostic; unsound)
- `CASCADE_SYM_INVERT_GENS=1` — apply g⁻¹ instead of g (diagnostic)

## Tests

**122 passing, 1 ignored** (documented overlay convention test).

- 109 lib tests
- 3 composite_parity integration (bit-identical bare-vs-composite)
- 3 online_sym_integration (propagator live inside CaDiCaL)
- 2 satsuma_generators (real satsuma binary on R(3,3)/K_6 and K_9)
- 5 proof-log unit tests
- 1 overlay_convention (`#[ignore]`, documents the SBP discrepancy)

## RFC

Full design: `docs/rfc/0001-online-symmetry-propagator.md`.
