# logic-zig status

**Version:** 0.21.0  
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

## Universal platform (v0.21)

| Piece | Maturity | Role |
|-------|----------|------|
| `sat/*` CDCL + IPASIR + DRAT | engine | Computational core |
| `circuit/*` BMC/kind/PDR/klive | engine | Sequential MC |
| `taxonomy/registry` | engine | Named systems × maturity |
| `deductive/natded` | fragment | Fitch natural deduction |
| `deductive/sequent` | fragment | LK sequents |
| `deductive/sequent_search` | fragment | Backward-chaining search |
| `deductive/focusing` | fragment | Andreoli focusing phases |
| `abductive/abduce` | fragment | Exhaustive ≤16 |
| `abductive/industrial` | fragment | Greedy hitting-set |
| `abductive/mus` | fragment | Complete MUS + Berge HS |
| `inductive/induction` | fragment | Math induction + datatypes |
| `constructive/intuitionistic` | fragment | IPC Kripke; LEM fails |
| `substructural/linear` | fragment | ILL + resource bags |
| `modal/kripke` | fragment | Modal K |
| `modal/epistemic_deontic` | fragment | Kᵢ + O/P |
| `fuzzy/fuzzy` | fragment | t-norms + Kleene |
| `paraconsistent/lp` | fragment | Belnap-Dunn / LP |
| `probabilistic/prob` | fragment | Independence + Fréchet |
| `probabilistic/markov` | fragment | MLN weighted worlds |
| `description/alc` | fragment | ALC tableau spine |
| `description/shiq` | fragment | H+I+Q+trans roles |
| `historical/syllogistic` | fragment | 24 moods × 4 figures |
| `nonmonotonic/default` | fragment | Reiter defaults |
| `informal/argument` | fragment | Argument structure |
| `type_theory/tt` | skeleton | MLTT micro |
| `bridge/giants` | external | Peer discovery |

## Residuals (honest — ambition ≠ achievement)

| Ambition | Now |
|----------|-----|
| Full focused LJ/LK + HO unification | Prop polarity + phase drivers |
| Optimized SHIQ tableau (pairwise blocking) | Role hierarchy + Q AST |
| Lifted MLN / MC-SAT | Prop ≤12-atom enumeration |
| Partial MUS / CAMUS industrial scale | Deletion-minimal + Berge ≤16 |
| Relevance R / HOL / categorical | `documented` only |
| Industrial parity Kissat/Z3/Vampire | Giants discover + CaDiCaL scoreboard; **no parity claim** |
| Complete K/T/S4/S5 decision procedures | Finite K + epistemic frames; full modal museum open (issue #5) |

## Dependency graph

See [`GRAPH.md`](GRAPH.md).

https://github.com/SMC17/logic-zig
