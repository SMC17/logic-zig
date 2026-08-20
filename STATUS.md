# logic-zig status

**Version:** 0.24.0  
**North star:** executable museum and agent-trust kernel in Zig. SAT/MC is
substrate; completeness is local to a named system
([`docs/UNIVERSAL.md`](docs/UNIVERSAL.md)).

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig giants
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-hwmcc golden
```

## Zig-side residual closure (v0.24)

| Residual | Module | Status |
|----------|--------|--------|
| Pairwise blocking + ≥n | `description/pairwise` | **fragment** |
| HO pattern unification | `type_theory/huet` | **fragment** |
| WPLL objective | `probabilistic/wpll` | **fragment** |
| Modal forcing traces | `modal/trace` | **fragment** |
| KLM + ranked countermodels | `nonmonotonic/klm` | **fragment** |
| MV fixture schema (Lean differential) | `manyvalued/fixtures` | **fragment** |
| Lean oracle contract | `docs/LEAN_ORACLE.md` | documented |

## What remains outside pure Zig `main`

These need **external processes**, not more library spines:

| Item | Why |
|------|-----|
| Issue **#3** Lean↔Zig fixtures | Requires pinned Lean 4 + `lake build` + CI nanoda; Zig schema is ready |
| Issue **#5** museum Lean frame proofs | Requires Lean formalization of frame conditions |
| Issue **#6** upstream contributions | Human upstream PR loop (Aristotle/Lean projects) |
| PR **#2** museum draft | Rebase onto current `main` + evidence gates |
| Industrial parity Kissat/Z3/Vampire | Scoreboard only; never claimed |

## Platform (complete for admitted fragments)

**Engines:** CDCL, BMC/k-ind/PDR/klive, IPASIR, DRAT, taxonomy.  
**Fragments:** ND, sequent, focusing, search, abduction ladder, IPC, linear, relevance, K–S5 + certs + traces, epistemic/deontic, fuzzy/LP + fixtures, MLN + lifted + WPLL, ALC/SHIQ + subset/pairwise blocking, HOL + resolution + pattern unify, categorical, syllogistic, defaults, KLM countermodels.

Cite: [`CITATION.cff`](CITATION.cff). Graph: [`GRAPH.md`](GRAPH.md). Lean: [`docs/LEAN_ORACLE.md`](docs/LEAN_ORACLE.md).

https://github.com/SMC17/logic-zig
