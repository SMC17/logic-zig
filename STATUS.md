# logic-zig status

**Version:** 0.19.0  
**North star:** universal logic library in Zig (`docs/UNIVERSAL.md`) — leave no stone unturned; stand on giants; deepen forever.

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig giants
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat --limit 15 --conflicts 150000
./zig-out/bin/logic-zig api-info
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
| `docs/UNIVERSAL.md` | Destination + non-fiction rules |

## Computational depth (unchanged spine)

SAT/MC/SMT/FOL industrial program: `docs/INDUSTRIAL.md`  
Taxonomy map: `docs/TAXONOMY_COVERAGE.md`

## Residuals (honest — ambition ≠ achievement)

| Ambition | Now |
|----------|-----|
| Universal coverage of taxonomy | Registry + spines; most families `documented`/`skeleton` |
| Peircean triad | All three modes real: propositional + first-order (ALP) abduction, SAT-exact + Bayesian induction. Residual: no probabilistic ALP, no ILP over clauses, no MCMC/graphical models |
| Nonmonotonic family | Default logic + rational closure shipped; residual: circumscription, autoepistemic, ASP stable models, argumentation frameworks, AGM revision |
| MaxSAT | Exact at explanation scale; **no industrial MaxSAT parity claim** (no core-guided/stratified engine) |
| Informal argument analysis | Structure OK; no NLP / full schemes library |
| Full type theory / proof assistant | Micro checker only |
| Beat Kissat/ABC/Z3/Vampire | Giants discover + CaDiCaL scoreboard; **no parity claim** |
| Philosophical completeness | Rows exist; engines mostly future |

https://github.com/SMC17/logic-zig
