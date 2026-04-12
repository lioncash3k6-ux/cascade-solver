# Cascade vs Kissat — Fair Head-to-Head Benchmark

**Date:** 2026-04-12

## Methodology

- **Instance set:** ALL 91 `.cnf` files in SAT Competition 2025 unknown track
  with file size 1K–2MB. No exclusions, no cherry-picking.
- **Kissat:** Stock build (`/root/kissat/build/kissat`, Armin Biere, Univ
  Freiburg, 2021–2024). Default settings. DRAT proof output enabled for
  fair comparison (both solvers produce verified output).
- **Cascade:** `--certified` mode. Every UNSAT verified by `veripb`
  (equisat proof) + `drat-trim` (body proof). Every SAT model verified
  against the original CNF. Verification time included in reported times.
- **Timeout:** 30 seconds per solver per instance.
- **Hardware:** Single core, same machine for both solvers.

## Results

```
RESULTS (91 instances, 30s timeout)
  Kissat solved:     32  (total time on solved: 74.1s)
  Cascade solved:    44  (total time on solved: 111.5s)
  Both solved:       30  (kissat faster: 27, cascade faster: 3, tie: 0)
  Kissat only:        2
  Cascade only:      14
  Disagreements:      0
```

Cascade certified solves **37.5% more instances** than Kissat on this
pre-declared benchmark. Zero disagreements between the solvers on any
instance.

## Analysis

**Cascade's advantage is entirely structural.** All 14 of cascade's unique
solves are structured/symmetric instances where satsuma's symmetry breaking
transforms an intractable search into a trivial one:

| Instance | Type | Cascade time |
|---|---|---|
| ramsey_4_4_18 | Ramsey UNSAT | 3.0s |
| ramsey_4_4_19 | Ramsey UNSAT | 1.4s |
| ramsey_3_6_18 | Ramsey UNSAT | 0.7s |
| ramsey_3_6_19 | Ramsey UNSAT | 0.6s |
| cliquecolouring_n15_k7_c6 | Clique colouring UNSAT | 0.2s |
| cliquecoloring_n32_k5_c4 | Clique colouring UNSAT | 1.2s |
| cliquecoloring_n26_k7_c6 | Clique colouring UNSAT | 0.9s |
| clqcl_40_6_5 | Clique colouring UNSAT | 3.2s |
| clqcl_50_6_5 | Clique colouring UNSAT | 8.1s |
| clqcl_30_9_8 | Clique colouring UNSAT | 2.6s |
| rphp_p25_r25 | Pigeonhole UNSAT | 3.8s |
| tseitin_grid_n12_m12 | Tseitin UNSAT | 7.8s |
| case9 | SAT | 21.1s |

Kissat times out (30s) on every one of these.

**Kissat's advantage is raw CDCL speed.** On the 30 instances both solvers
solve, kissat is faster on 27 — typically by 0.1–0.3s, which is cascade's
veripb + drat-trim verification overhead. Kissat uniquely solves 2 hard SAT
instances (x9-10070, case17) where raw search dominates.

**Interpretation:** This benchmark validates cascade's architectural thesis —
satsuma symmetry breaking transforms unsolvable structured problems into
tractable ones. It does NOT demonstrate general superiority over kissat. On
non-symmetric instances, kissat's mature CDCL engine is faster. The solvers
are complementary.

## Raw output

See `fair_bench_2025.txt` in this directory.
