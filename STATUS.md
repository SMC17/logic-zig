# logic-zig status

**Version:** 0.22.0  
**North star:** universal logic library in Zig ([`docs/UNIVERSAL.md`](docs/UNIVERSAL.md)) — leave no stone unturned; stand on giants; deepen forever.

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig giants
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig api-info
./zig-out/bin/logic-hwmcc golden
```

## Platform (v0.22)

| Piece | Maturity | Role |
|-------|----------|------|
| CDCL SAT / IPASIR / DRAT | engine | Computational core |
| BMC / k-ind / PDR / k-liveness | engine | Sequential MC |
| taxonomy registry | engine | Named systems × maturity |
| ND / sequent / search / focusing | fragment | Formal deduction |
| Abduction ladder (≤16 / industrial / MUS) | fragment | Explanations |
| IPC / linear / relevance | fragment | Constructive + substructural |
| Modal K + **K/T/S4/S5 finite decision** | fragment | Normal modal |
| Epistemic / deontic | fragment | Agency modalities |
| Fuzzy / LP | fragment | Many-valued |
| Independence + MLN | fragment | Probabilistic |
| ALC + SHIQ | fragment | Description logics |
| Syllogistic / defaults | fragment | Historical + nonmonotonic |
| **HOL micro** (STLC + β) | fragment | Higher-order spine |
| **Categorical / topos witnesses** | fragment | Algebraic logic |
| MLTT micro | skeleton | Type theory |
| Giants interop | external | Peer discovery |

## Residuals

| Ambition | Now |
|----------|-----|
| Full HOL resolution / Isabelle parity | STLC + β only |
| Constructed topos / sheaves | Finite categories + axiom witnesses |
| Modal certificates + Lean frame proofs | Exhaustive ≤4-world decision |
| Industrial MUS scale | ≤16 abducibles complete |
| Solver parity claims | Scoreboard only; no parity |

See [`GRAPH.md`](GRAPH.md). Cite via [`CITATION.cff`](CITATION.cff).

https://github.com/SMC17/logic-zig
