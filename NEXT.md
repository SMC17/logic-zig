# NEXT — logic-zig

_Last update: 2026-07-21 by Hermes_

## What just shipped

`dynamic-pdl` is now a `verified_exhibit` (v0.23.0):

- `src/modal/pdl.zig` implements Propositional Dynamic Logic on finite frames:
  programs `α ::= a | α;β | α∪β | α* | φ?` and modalities `[α]φ` / `⟨α⟩φ`.
- Two independent evaluators (`evalMatrix` via relation RTC, `evalReach` via
  Fischer–Ladner graph reach) are cross-checked over hundreds of randomized
  formulas/models and must agree.
- `findCounter` is a brute-force exhaustive-frame oracle: it enumerates every
  frame up to a bound and confirms PDL validities (K, distribution, composition,
  union, star unroll, star induction, test equivalence, diamond-star fixpoint)
  and produces concrete countermodels for known non-validities.
- `verifyClaim` replays a recorded verdict against both engines and fails closed
  on any divergence. Six unit tests pass beside the module.
- Registry `dynamic-pdl` promoted `documented → fragment`; museum promotion
  derived to `verified_exhibit`; api/v1 → 1.6.0 with `modal_pdl` capability bit.
- Evidence contract: `docs/exhibits/pdl.md`.

## Next concrete action

The next cheap stone from the documented backlog is one of:

- `hybrid-logic` (nominals + @, satisfaction operators) on finite frames, or
- `mu-calculus` (least/greatest fixpoint model checking) on finite transition
  systems — a natural follow-on to PDL since PDL embeds into the μ-calculus.

Pre-register with `stax-experiment register --lane logic-zig`, wire api/v1 1.7.0,
add a taxonomy row, and follow the register→build→verify→exhibit loop used for PDL.

## In-flight hypotheses

None — all logic-zig registers have verdicts.

## Context that won't be obvious from git

- Zig 0.16 idioms: `ArrayList = .empty`, append takes allocator, `var` that's
  never reassigned must be `const` (compile error), no standalone
  `zig test src/...` (module paths) — always `zig build test`.
- Recurring lesson (3× this session): **mutate-and-restore on shared backtracking
  state is a bug factory** — prefer immutable snapshot contexts.
- `test` is a reserved keyword in Zig — program-test builders use `test_`; the
  `Arena` program builder is `mkprog` to avoid shadowing `prop`'s `p` parameter.
- A transient `zig build test` failure appeared once (seed-dependent?) early in
  v0.22 and never reproduced across ~12 subsequent green runs. If it recurs,
  capture the seed from the failing command line.
- The "c parse error: InvalidFormat" line in test output is an existing
  negative-path test elsewhere, not a failure.
- Remaining big lifts (deliberately deferred): relevance R (undecidable — needs a
  bounded fragment decision), HOL, categorical logic. Cheap next stones after PDL:
  hybrid logic, μ-calculus, possibilistic logic, autoepistemic expansions, natural
  logic monotonicity calculus.
- Taxonomy registry test enforces ≥5 documented rows (honest-placeholder guard):
  when advancing rows to fragment, add newly named documented rows rather than
  weakening the assertion.
