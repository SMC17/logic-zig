# logic-zig status

**Version:** 0.20.0  
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

## Universal platform (v0.20)

| Piece | Role |
|-------|------|
| `constructive/intuitionistic` | IPC finite Kripke; LEM fails |
| `substructural/linear` | ILL connectives + resource accounting |
| `modal/epistemic_deontic` | Multi-agent K_i + deontic O/P |
| `probabilistic/prob` | Independence eval + Fréchet bounds |
| `description/alc` | ALC concepts + tableau clash spine |
| `deductive/sequent_search` | Backward-chaining LK proof search |
| `abductive/industrial` | Hitting-set abduction past ≤16 |
| (+ all v0.18–0.19 spines) | ND, sequent, fuzzy, LP, syllogistic, defaults, … |

## Residuals (honest)

| Ambition | Now |
|----------|-----|
| Full IPC proof search | Kripke eval only |
| Focusing linear logic prover | Resource bag + AST |
| Dynamic epistemic / STIT | Static multi-agent frames |
| Markov logic / probabilistic programming | Independence + Fréchet |
| SHIQ / OWL reasoner | ALC ∧-expansion + clash |
| Industrial focusing / inverse method | Depth-bounded invertible rules |
| Complete minimal hitting-set abduction | Greedy cores + prune |

https://github.com/SMC17/logic-zig
