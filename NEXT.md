# NEXT — logic-zig

_Last update: 2026-07-17 by Claude_

## What just shipped

Five releases in one session, all on `main`:

- `57ee0db` v0.18.0 — Peircean triad: propositional abduction (MARCO, subset-minimal) + minimal-k DNF induction
- `ad10d9a` v0.19.0 — MaxSAT engine, min-cost abduction (implicit hitting set), first-order ALP, Bayesian induction, Reiter defaults, KLM rational closure
- `9f19cfb` v0.20.0 — Dung argumentation, ASP stable models, AGM revision, circumscription, analogical proportions
- `c897021` v0.21.0 — G4ip intuitionistic prover, many-valued matrices (K3/LP/FDE/Ł3), epistemic S5 + common knowledge + announcements, complete syllogistic decision, EL subsumption
- `2b1346d` v0.22.0 — MLL linear logic prover, deontic SDL (KD), registry widened to 61 systems

18 pre-registered experiments, all confirmed; 3 Type-I errors self-caught by their
falsifiers before ship (MaxSAT descent-to-zero status, analogy XOR overclaim, G4ip
context corruption). api/v1 now 1.5.0 with 40 capability bits (u64, low word stable).
Registry: 27 fragment / 10 engine / 15 documented / 3 skeleton / 6 external.
**Not pushed to GitHub** — user has not asked; local commits only.

## Next concrete action

Pick the top row from the documented backlog and repeat the register→build→verdict
loop: implement `src/modal/pdl.zig` (propositional dynamic logic: finite-model
evaluation of [α]φ with α ::= atomic | α;β | α∪β | α* via reachability, canon:
[α*]φ fixpoint, induction axiom), pre-registering with `stax-experiment register
--lane logic-zig` first, wiring api/v1 1.6.0 + taxonomy row `dynamic-pdl` → fragment.

## In-flight hypotheses

None — all 20 logic-zig registers have verdicts (2 stale ones from v0.13/v0.17
sessions closed 2026-07-17 with current-suite evidence).

## Context that won't be obvious from git

- Zig 0.16 idioms: `ArrayList = .empty`, append takes allocator, `var` that's
  never reassigned must be `const` (compile error), no standalone
  `zig test src/...` (module paths) — always `zig build test`.
- Recurring lesson (3× this session): **mutate-and-restore on shared backtracking
  state is a bug factory** — prefer immutable snapshot contexts (see
  `reason/alp.zig` solveG and `logic/intuitionistic.zig` proveSeq rewrites).
- A transient `zig build test` failure appeared once (seed-dependent?) early in
  the session and never reproduced across ~12 subsequent green runs. If it
  recurs, capture the seed from the failing command line.
- The "c parse error: InvalidFormat" line in test output is an existing
  negative-path test elsewhere, not a failure.
- Remaining big lifts (deliberately deferred, listed as documented): relevance R
  (undecidable — needs a bounded fragment decision), HOL, categorical logic.
  Cheap next stones: PDL, possibilistic logic, autoepistemic expansions, natural
  logic monotonicity calculus, hybrid logic.
- Taxonomy registry test enforces ≥5 documented rows (honest-placeholder guard):
  when advancing rows to fragment, add newly named documented rows rather than
  weakening the assertion.
