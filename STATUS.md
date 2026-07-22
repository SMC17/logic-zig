# logic-zig status

**Version:** 0.23.0  
**North star:** executable museum and comparative laboratory implementing every
branch of logic in Zig. “Complete” is scoped to evidence-bearing exhibit contracts
(`docs/MUSEUM.md`), never inferred from registry breadth.

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig museum
./zig-out/bin/logic-zig giants
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat --limit 15 --conflicts 150000
./zig-out/bin/logic-zig api-info
( cd lean && lake build )
```

## Universal platform (v0.17)

| Piece | Role |
|-------|------|
| `taxonomy.registry` | Named systems × maturity across the master taxonomy |
| `informal/argument` | Premise/conclusion/schemes structure |
| `type_theory/tt` | MLTT micro kernel (check) |
| `modal/kripke` | Finite-frame K / diamond-box |
| `bridge/giants` | Discover CaDiCaL, Kissat, Z3, ABC, Vampire, Lean, … |
| `reason/abduction` | Subset-minimal + **min-cost** explanations (MARCO / implicit hitting set) |
| `reason/induction` | Minimal-k DNF synthesis from examples (SAT-exact, re-verified) |
| `reason/alp` | First-order abduction: SLD over Horn clauses, denials, Δ instantiation |
| `reason/bayes` | Exact Bayesian posterior over conjunctions; Laplace succession |
| `reason/default_logic` | Reiter extensions (grounded/stable), credulous/skeptical |
| `reason/klm` | Rational closure: exceptionality ranks, SAT-backed queries |
| `sat/maxsat` | Weighted partial MaxSAT (exact descending-bound, SWC encoding) |
| `reason/argumentation` | Dung AFs: grounded/complete/stable/preferred + acceptance |
| `reason/asp` | Stable models (Gelfond–Lifschitz reduct certificate) |
| `reason/agm` | AGM base contraction/revision via remainder sets |
| `reason/circumscription` | P-minimal-model entailment (fixed/varying atoms) |
| `reason/analogy` | Boolean analogical proportions, solving, abstaining classifier |
| `logic/intuitionistic` | G4ip decision procedure (Glivenko-verified) |
| `logic/manyvalued` | K3 / LP / FDE / Ł3 finite-matrix consequence |
| `modal/epistemic` | Multi-agent S5, common knowledge, announcements |
| `logic/syllogistic` | Complete 256-form categorical decision (15/24) |
| `logic/el` | EL subsumption via completion rules |
| `modal/deontic` | SDL (KD): D⇔seriality, Ross canon |
| `logic/linear` | MLL sequent prover: no weakening/contraction, no MIX |
| `modal/pdl` | PDL: [α]φ/⟨α⟩φ for α::=a|α;β|α∪β|α*|φ? on finite frames; two semantics + exhaustive oracle |
| `docs/UNIVERSAL.md` | Destination + non-fiction rules |

## Computational depth (unchanged spine)

SAT/MC/SMT/FOL industrial program: `docs/INDUSTRIAL.md`  
Taxonomy map: `docs/TAXONOMY_COVERAGE.md`

## Truth-reset work in progress

- Inductive-invariant verification now checks `I => !Bad`, rejects inconclusive
  initiation/consecution queries, and no longer converts k-induction into an empty
  invariant certificate.
- SAT conflict limits and reported counters reset per solve call.
- Assumption-core minimality and uniqueness are tri-state; inconclusive deletion
  probes can no longer silently promote either property to true.
- Proof-producing assumption solves record their ordered assumption context and
  reinitialize proof state for every incremental call.
- Combinational equivalence preserves `unknown` instead of reporting a false
  inequivalence.
- Scoreboard and trust gates require actual external evidence.
- IPASIR preserves unterminated clauses, accepts empty clauses, records sticky C-ABI
  failures, and implements termination and learned-clause callbacks. A compiled C
  consumer exercises those contracts in `zig build test`; assumption-proof lifecycle
  and a fully specified state machine remain incomplete, so the registry says fragment.
  IPASIR `signature()` now reports `logic-zig-ipasir-1.0`.
- FOL evaluator binder environments now use `TermId` and restore scope. SAT-backed
  constants have proper decision variables, model reconstruction, and replay;
  functional terms now compose inside predicate atoms (arity remains limited to two).
  The finite-model finder's module header now states its honest scope (symbols keyed
  by `(name,arity)`, missing constants → `error.Unbound`, domain cap 4).
- Public `isTautology`/`areEquivalent` root helpers are tri-state (`?bool`, `null` =
  solver `unknown`); they no longer fold `unknown` into `false`.
- Evidence-bearing museum manifests exist for classical propositional logic, S4,
  and first-order logic. Classical propositional logic is the first
  `verified_exhibit`: producer proofs cross a serialized, search-independent RUP
  checker and a formal exhibit contract. Aristotelian categorical syllogistic is
  also a `verified_exhibit`: every one of 512 form/semantics combinations emits
  replayable exhaustive evidence or a countermodel. These are audited/unit-tested,
  not formally verified.
- K3, LP, FDE, and L3 finite-matrix consequence are `verified_exhibit` contracts:
  decisions validate matrix/formula shape, exhaust the finite valuation space, and
  return replayable countervaluations. The explicit limit is eight atoms per query.
- Finite Dung argumentation is a `verified_exhibit` for exact admissible, complete,
  grounded, stable and preferred extensions plus credulous/skeptical acceptance.
  Evidence replay rejects omissions and duplicates; all 512 three-argument attack
  relations are exhaustively checked. The implementation remains exponential and
  makes no ICCMA-scale claim.
- Propositional normal ASP is a `verified_exhibit`: every stable-model list is
  checked for both soundness and omitted models by replaying the Gelfond-Lifschitz
  reduct across the finite carrier. Its contract excludes grounding, disjunction,
  aggregates, optimization, ASP-Core-2 interoperability and industrial scale.
- Propositional Dynamic Logic is a `verified_exhibit` for finite-frame semantics
  of [α]φ/⟨α⟩φ over regular programs α::=a|α;β|α∪β|α*|φ?. Two independent
  evaluators (matrix reflexive-transitive closure and Fischer–Ladner graph
  reach) are cross-checked over randomized formulas/models, a brute-force oracle
  confirms validities/non-validities on all frames up to small bounds, and
  `verifyClaim` replays a verdict against both engines and fails closed on any
  divergence. The contract excludes a parser, a Segerberg Hilbert calculus and
  proof objects, converse/intersection/hybrid PDL, and models over 16 worlds or
  8 atomic programs.
- Finite propositional Reiter default logic is a `verified_exhibit` for CNF facts
  and cube defaults. Exact generating-set replay checks groundedness,
  justification consistency, stability and omissions; arbitrary formula and
  first-order defaults remain outside the contract.
- Finite AGM belief-base change is a `verified_exhibit`: remainder families are
  checked for maximality and omissions, all three partial-meet policies replay,
  and cube revision is verified through the Levi identity. Deductively closed
  theories and iterated revision remain separate contracts.
- Finite propositional circumscription is a `verified_exhibit`: validated
  minimized/fixed partitions produce exact minimal-signature evidence, and every
  refutation carries a complete minimal countermodel. Random CNFs remain checked
  against the independent full-assignment oracle.
- KLM rational closure now propagates inconclusive SAT checks, bounds scratch
  allocation to one rank level, validates ranking shape, and replays exact ranks
  and query levels. It remains catalog-only until refutations carry ranked
  countermodels rather than only Boolean/level evidence.
- `logic-zig museum` also prints every uncontracted taxonomy row as a catalog-only
  restoration backlog, keeping the whole landscape visible without promoting it.
- The first Lean oracle project formalizes the K3, LP, FDE and L3 separating
  examples and Boolean-preservation lemmas under Lean 4.28.0. Local `lake build`
  passes; CI is configured to add nanoda independent checking with `sorryAx`
  forbidden. An Aristotle audit task has been submitted, but its output is not
  evidence until downloaded, reviewed and kernel-checked.
- GitHub CI now builds pinned CaDiCaL, DRAT-trim and ABC trust anchors instead of
  invoking the fail-closed trust report in an environment where they are absent.
  Structured issue forms, PR evidence gates, security policy, code ownership,
  Dependabot configuration and citation metadata are present on the frontier PR.

## Residuals (honest — ambition ≠ achievement)

| Ambition | Now |
|----------|-----|
| Universal coverage of taxonomy | Registry + spines; most families `documented`/`skeleton` |
| Peircean triad | All three modes real: propositional + first-order (ALP) abduction, SAT-exact + Bayesian induction. Residual: no probabilistic ALP, no ILP over clauses, no MCMC/graphical models |
| Nonmonotonic family | Defaults, rational closure, ASP, circumscription, argumentation, AGM all shipped as fragments; residual: autoepistemic logic, inheritance networks, truth maintenance, industrial ASP/ICCMA scale |
| MaxSAT | Exact at explanation scale; **no industrial MaxSAT parity claim** (no core-guided/stratified engine) |
| Modal / dynamic / temporal | K/S4 finite-frame eval; epistemic S5 + common knowledge + announcements; deontic SDL; **PDL finite-frame semantics `verified_exhibit`**; **bounded LTL (X/F/G/U/R) `verified_exhibit`** (two-semantics + cross-check oracle); **bounded PLTL (Y/Z/S/B past-time) `verified_exhibit`** extends LTL with past operators, same two-semantics + exhaustive oracle. Residual: no PDL parser/Segerberg calculus, no converse/intersection/hybrid PDL, no CTL* / full μ-calculus exhibit |
| Informal argument analysis | Structure OK; no NLP / full schemes library |
| Full type theory / proof assistant | Micro checker only |
| Lean / Aristotle oracle | Initial finite-matrix formalization builds locally; CI and Aristotle result still need public receipts |
| Beat Kissat/ABC/Z3/Vampire | Giants discover + CaDiCaL scoreboard; **no parity claim** |
| Philosophical completeness | Rows exist; engines mostly future |

https://github.com/SMC17/logic-zig
