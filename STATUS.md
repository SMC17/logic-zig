# logic-zig status

**Version:** 0.18.0  
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

## Universal platform (v0.18)

| Piece | Role |
|-------|------|
| `taxonomy.registry` | Named systems × maturity across the master taxonomy |
| `informal/argument` | Premise/conclusion/schemes structure |
| `type_theory/tt` | MLTT micro kernel (check) |
| `modal/kripke` | Finite-frame K / diamond-box |
| `abductive/abduce` | Propositional minimal explanations via CDCL |
| `inductive/induction` | Math induction schema + Peano/list datatypes |
| `fuzzy/fuzzy` | Many-valued / fuzzy t-norms (Gödel, product, Łukasiewicz) + Kleene |
| `bridge/giants` | Discover CaDiCaL, Kissat, Z3, ABC, Vampire, Lean, … |
| `docs/UNIVERSAL.md` | Destination + non-fiction rules |

## Computational depth (unchanged spine)

SAT/MC/SMT/FOL industrial program: `docs/INDUSTRIAL.md`  
Taxonomy map: `docs/TAXONOMY_COVERAGE.md`

## Residuals (honest — ambition ≠ achievement)

| Ambition | Now |
|----------|-----|
| Universal coverage of taxonomy | Registry + spines; induction/abduction/fuzzy now **fragment** |
| Informal argument analysis | Structure OK; no NLP / full schemes library |
| Full type theory / proof assistant | Micro checker only |
| Beat Kissat/ABC/Z3/Vampire | Giants discover + CaDiCaL scoreboard; **no parity claim** |
| Philosophical completeness | Rows exist; engines mostly future |
| Industrial-scale abduction | ≤16 abducibles exhaustive; hitting-set / iterative MUS later |
| Statistical / Bayesian induction | Mathematical induction only so far |

https://github.com/SMC17/logic-zig
