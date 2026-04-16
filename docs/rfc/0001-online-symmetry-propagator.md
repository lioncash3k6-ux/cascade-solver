# RFC-0001 — Online Symmetry Propagator

- Status: **Draft**
- Target: cascade v0.6
- Authors: cascade team
- Created: 2026-04-16
- Supersedes: the offline satsuma → augmented-CNF pipeline (v0.5)

## 1. Summary

Promote symmetry breaking from a compile-time preprocessing step
(`satsuma` produces SBP clauses appended to the CNF) to a runtime
IPASIR-UP propagator that enforces *lex-leader ordering under the
automorphism group G* dynamically against the current partial trail.

The offline generator-detection pass (satsuma/dejavu) is **kept**; we
only replace the static SBP emission with online enforcement.

## 2. Motivation

Offline SBP has three known pathologies that dominate hard Ramsey runs:

1. **Static approximation.** SBP clauses encode a fixed lex-leader
   relative to a fixed variable ordering. Under CDCL branching, the
   "natural" order of assignment diverges from the SBP's canonical
   order within a few hundred conflicts. Most SBP clauses are never
   consulted.
2. **Propagation dilution.** SBP aux variables land in the clause DB
   as ordinary clauses. They participate in BCP at the same priority
   as combinatorial clauses, so their symmetry signal is smeared
   across VSIDS rather than concentrated at the symmetry frontier.
3. **Proof bloat.** The satsuma VeriPB prefix is O(|G|·|V|) bits
   regardless of which generators are actually exercised during
   search. An online emitter only certifies the generators that
   actually fired.

Online enforcement attacks all three: the comparator is recomputed
against the live trail, conflicts fire *only* when a branch has
become non-canonical, and proof obligations are emitted lazily.

## 3. Non-goals

- Not replacing `satsuma`'s *detection* phase. We consume its
  generator output.
- Not implementing orbit-closed clause learning (every learned clause
  replicated across G). That is RFC-0002 territory; blocks on this
  landing first.
- Not general-CNF. Targeted at instances where G is transitive or
  near-transitive on observed vars (Ramsey, pigeonhole, packing,
  mutilated board). Non-symmetric instances hit a no-op fast path.

## 4. Background

`cascade` v0.5 already runs an IPASIR-UP external propagator,
`BicliquePropagator`, inside in-process CaDiCaL 2.2.1 (see
`src/propagator.rs`, `src/cadical.rs`). The FFI vtable
(`src/cadical_ffi.cpp`) exposes six of the nine IPASIR-UP callbacks;
external-clause addition
(`cb_has_external_clause`/`cb_add_external_clause_lit`) is present in
the struct but unwired. Backend currently connects a single
propagator; that will change.

The satsuma binary is invoked from `src/symmetry/satsuma.rs` and emits
(a) an augmented CNF and (b) a VeriPB equisat proof. We will parse
the *generators* instead of consuming the augmented CNF.

## 5. Design

### 5.1 Data structures

```rust
// src/symmetry/generators.rs (new)
pub struct Permutation {
    // Dense Vec<Var> representation: image[v] = g(v) for v in 1..=n.
    // Polarity-flipping generators use signed Lit images.
    image: Vec<i32>,
}

impl Permutation {
    pub fn apply_var(&self, v: u32) -> i32 { self.image[v as usize] }
    pub fn apply_lit(&self, l: i32) -> i32 {
        let v = l.unsigned_abs() as usize;
        let g = self.image[v];
        if l > 0 { g } else { -g }
    }
}

pub struct GeneratorSet {
    pub gens: Vec<Permutation>,
    pub n_vars: u32,
    pub ordering: Vec<u32>, // var -> rank in lex-leader order
}
```

### 5.2 Lex comparator (per generator, per level)

The heart of online lex-leader. For a fixed variable ordering
`v_1 < v_2 < … < v_n` and a generator g, define the lex order on
assignments: an assignment A is the *lex-leader of its orbit* iff
for every g ∈ G, `A ≤_lex g(A)`.

Dynamic check: walk the trail in order of `ordering`, compare
`val(v_i)` vs `val(g(v_i))`. Three outcomes per variable:

- `val(v_i) < val(g(v_i))` → definitively OK, halt comparator for
  this generator at this trail state; re-enable if backjump undoes
  v_i.
- `val(v_i) > val(g(v_i))` → **conflict**. Current branch is
  non-canonical. Emit blocking clause (see §5.4).
- `val(v_i) == val(g(v_i))` → continue to next position.
- `v_i` unassigned but `val(g(v_i))` known to be 1, or vice versa
  → **propagation**: we can force `val(v_i)` to restore canonicality.

We store the comparator's *frontier index* — the position along
`ordering` it has walked to so far. On backtrack we rewind the
frontier.

```rust
pub struct LexComparator {
    gen_idx: usize,
    frontier: u32,    // next ordering position to examine
    status: CmpStatus, // Satisfied | Undecided | Violated
}

enum CmpStatus { Satisfied, Undecided, Violated }
```

One `LexComparator` per generator. On any observed-var assignment we
notify the set of comparators whose frontier variable is touched
(precomputed reverse index: `var → Vec<comparator_idx>`).

### 5.3 Propagation and conflict

Per IPASIR-UP cycle:

1. `notify_assignment(lits)` — for each lit, find every comparator
   whose frontier is at `var(lit)` or at `g(var(lit))` for some g.
   Advance comparators; queue propagations and conflicts.
2. `propagate()` — drain propagation queue; for each, build a reason
   clause (see §5.4) and return the literal.
3. `check_found_model(m)` — verify that m is the lex-leader of its
   orbit. O(|G|·n). Rejects non-canonical models as a safety net;
   under correct design this never fires.

### 5.4 Reason and conflict clauses (soundness contract)

A lex-violation at position i under generator g produces a blocking
clause that negates the trail prefix responsible:

```
¬(v_1 = a_1) ∨ ¬(v_2 = a_2) ∨ … ∨ ¬(v_i = a_i)
```

This clause is implied by the symmetry of F under g: if a lex-smaller
equivalent exists, F|trail SAT iff F|g(trail) SAT, so the current
branch loses no models.

**Proof-safety note.** This clause is not RUP against F alone — it
requires the generator g as an auxiliary fact. We certify it via a
VeriPB substitution-redundancy step (`red` rule) with g as the
witness. The same mechanism satsuma uses; we emit it online instead
of up-front.

### 5.5 Composition with BicliquePropagator

CaDiCaL supports only one external propagator. We introduce:

```rust
// src/propagator/composite.rs (new)
pub struct CompositePropagator {
    subs: Vec<Box<dyn ExternalPropagator>>,
    /// drain order for propagate(): round-robin index
    cursor: usize,
}
```

- `notify_assignment`, `notify_new_decision_level`,
  `notify_backtrack` fan out to every sub.
- `propagate` drains subs round-robin (fair, prevents starvation
  under adversarial ordering).
- `add_reason_clause_lit` routes by tagging propagated lits: the
  composite owns a `HashMap<Lit, sub_idx>` populated when a sub
  returned the lit from `propagate()`.
- `check_found_model` is the logical AND across subs.

Current `BicliquePropagator` gains no changes. The composite is a
drop-in replacement for the current `Box<dyn ExternalPropagator>`
argument of `Solver::connect_propagator`.

### 5.6 Proof emission

On solver startup (before first `solve()`):
  1. Run satsuma in generator-only mode: `satsuma --file=... --print-generators`.
  2. Parse generators → `GeneratorSet`.
  3. Emit VeriPB preamble declaring the witnesses (one `red` step per
     generator, marking it as a proof-level symmetry).

On conflict fired by a `LexComparator`:
  4. Emit the VeriPB substitution step `red ... ; a ... ;` pairing
     the learned blocking clause with the responsible generator.

These steps interleave with CaDiCaL's DRAT/LRAT body proof. Two
sinks, one ordered file. The existing proof composer in
`src/certify.rs` + `src/card_proof.rs` gets a third contributor.

### 5.7 Fallback and bypass

Feature flag `--online-sym={on,off,hybrid}`:
- `off`: v0.5 behavior, offline SBP via satsuma augmented CNF.
- `on`: v0.6 behavior, generators-only, no SBP clauses in CNF.
- `hybrid`: emit half the SBP clauses (say, those generated by the
  largest orbits) and leave the long tail to online enforcement.

Default is `off` for the certified pipeline until 4/4 Ramsey
benchmarks pass under `on`.

## 6. Soundness argument

Let F be the formula, G the detected automorphism group, π =
(a_1,a_2,…,a_k) the current trail (projected to observed vars in
trail order), and ≤_lex the lex order induced by `ordering`.

**Invariant.** At every search state, for every generator g ∈ G, the
comparator `Cmp[g]` reflects the ≤_lex relationship between
`π|_frontier` and `g(π)|_frontier`.

**Conflict soundness.** If `Cmp[g]` declares `π >_lex g(π)` strictly
at position i, then there exists an orbit-equivalent assignment g(π)
that is lex-smaller. The blocking clause
`¬(v_1=a_1) ∨ … ∨ ¬(v_i=a_i)` is entailed by `F ∧ g·F = F`, i.e.,
by the fact that g is an automorphism. This is the standard
lex-leader SBP argument (Crawford-Ginsberg '96), applied dynamically
to the live trail prefix rather than to all permutations upfront.

**Propagation soundness.** Same argument: if the only way to avoid
violating `π ≤_lex g(π)` at position i is `val(v_i) = c`, then c is
forced by `F ∧ automorphism(g)`.

**Completeness.** Not 100%. We check only single generators, not
arbitrary products in G. This is identical to satsuma's static SBP
and is known to leave some cosets unpruned. Orbit-closure (RFC-0002)
closes this.

**Proof-checkability.** Each blocking/propagating clause is paired
with the generator g used to justify it, emitted as a VeriPB `red`
substitution-redundancy step. `veripb` accepts such steps given the
witness. No clause enters the DRAT body proof without a matching
`red` line in the VeriPB prefix.

## 7. Interface changes

### 7.1 New modules

```
src/symmetry/
  mod.rs          (extended: new trait SymmetryGenerators)
  satsuma.rs      (extended: generator-extraction mode)
  generators.rs   (new)
  online.rs       (new: SymmetryPropagator struct)
src/propagator/
  mod.rs          (new: moves existing propagator.rs here)
  biclique.rs     (renamed from propagator.rs)
  composite.rs    (new)
```

### 7.2 CLI

```
cascade solve --online-sym=on [existing flags…]
cascade solve --online-sym=hybrid --hybrid-orbit-cutoff=128 …
```

### 7.3 Library API

```rust
// before (v0.5):
solver.connect_propagator(Box::new(bicl_prop), &observed);

// after (v0.6):
let mut comp = CompositePropagator::new();
comp.add(Box::new(bicl_prop));
comp.add(Box::new(sym_prop));
solver.connect_propagator(Box::new(comp), &observed);
```

## 8. Benchmarks and acceptance criteria

Gate on the existing 9-instance certified suite plus R(4,6) CnC:

| Instance      | v0.5 conflicts | v0.6 target | Proof still verifies |
|---------------|---------------:|------------:|---------------------:|
| R(3,3)/K_6    | 19             | ≤ 19        | yes                  |
| R(3,4)/K_9    | 0              | 0           | yes                  |
| R(3,5)/K_14   | 79             | ≤ 40        | yes                  |
| R(3,6)/K_18   | 2,480          | ≤ 1,500     | yes                  |
| R(4,4)/K_18   | 26,588         | ≤ 15,000    | yes                  |
| R(4,5)/K_25   | 122            | ≤ 122       | yes                  |
| R(4,6)/K_36   | CnC 16384 subs | 2× speedup  | yes                  |

"Proof still verifies" is the hard gate: `veripb` + `drat-trim` must
accept the composed proof. Conflict reductions are soft targets; the
hard requirement is **no regression** on any certified instance.

## 9. Staging plan

Five PRs, each individually mergeable:

1. **PR-1 — Composite propagator.** `CompositePropagator` + tests;
   no behavior change (single sub-propagator case). Unblocks wiring.
2. **PR-2 — Generator extraction.** `generators.rs` + satsuma's
   `--print-generators` parser. No solver integration yet.
3. **PR-3 — LexComparator.** Pure data structure, property tests
   against a reference naive implementation.
4. **PR-4 — SymmetryPropagator + wiring.** Turn on via
   `--online-sym=on`; run the 9-instance suite unverified; compare
   conflicts.
5. **PR-5 — Proof emission.** Hook VeriPB `red` steps into
   `certify.rs`; run the 9-instance suite **with** verification.
   This is the ship gate.

Budget: ~2 weeks of focused work, matching the user's v0.6
timeline.

## 10. Open questions

- **Q1.** Variable ordering `ordering: Vec<u32>` — does it need to
  match satsuma's internal SBP ordering for proof-checkability? Need
  to read dejavu's canonicalization code.
- **Q2.** Polarity-flipping generators (color-swap in Ramsey) —
  `Permutation` needs signed images. The VeriPB witness format
  supports this; Rust side needs audit.
- **Q3.** Hybrid mode tuning — what orbit-size cutoff maximizes the
  win? Expected ablation in PR-5 benchmarks.
- **Q4.** Thread-safety for future parallel CnC. Composite + sym
  propagator both hold per-thread mutable state; need `Sync` audit
  before the parallel conquer path in `src/conquer.rs` consumes
  them. Not blocking v0.6.

## 11. References

- Crawford, Ginsberg, Luks, Roy 1996 — "Symmetry-breaking predicates
  for search problems"
- Devriendt, Bogaerts, Bruynooghe, Denecker 2016 — "On local
  domain symmetry for model expansion" (dynamic SB in CP/ASP)
- Anders, Schweitzer 2024 — "Satsuma: structure-based symmetry
  breaking in SAT" (TACAS)
- Fazekas, Biere, Scholl 2019 — "IPASIR-UP: user propagators for
  CDCL" (API foundation)
- cascade v0.5-wip memory notes and `STATUS.md`
