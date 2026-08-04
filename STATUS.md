# logic-zig status

**Version:** 0.23.0  
**North star:** universal logic library in Zig ([`docs/UNIVERSAL.md`](docs/UNIVERSAL.md)).

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor taxonomy giants edge-suite trust-report api-info
./zig-out/bin/logic-hwmcc golden
```

## v0.23 depth attack

| Module | Role |
|--------|------|
| `modal/cert` | Validity + countermodel **certificates** with independent checkers + mutation test |
| `description/shiq_tableau` | ALC/SHIQ **tableau with subset blocking** |
| `probabilistic/lifted_mln` | **Lifted MLN** — FO weighted formulas → exhaustive grounding |
| `type_theory/hol_resolution` | **HOL resolution loop** — binary resolve + factor; refutes `{P},{¬P}` and chains |

## Platform spine (cumulative)

Engines: CDCL, BMC/k-ind/PDR/klive, IPASIR, DRAT, taxonomy.  
Fragments: ND, sequent, focusing, abduction ladder, IPC, linear, relevance, K–S5 decision + certs, epistemic/deontic, fuzzy/LP, MLN + lifted, ALC/SHIQ + blocking tableau, HOL micro + resolution, categorical, syllogistic, defaults.

## Residuals

| Ambition | Now |
|----------|-----|
| Modal Lean formalization | Zig certs only |
| Full SHIQ (Q/H) expansion + pairwise blocking | Subset blocking + ALC rules |
| KBMC / WPLL lifted inference | Exhaustive ground ≤ domain 4 |
| Huet HO unification | Rigid-head / prop-HO resolution |

Cite: [`CITATION.cff`](CITATION.cff). Graph: [`GRAPH.md`](GRAPH.md).

https://github.com/SMC17/logic-zig
