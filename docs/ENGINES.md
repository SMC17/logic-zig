# Engines reference

## CDCL SAT (`sat/solver.zig`)

Classic conflict-driven clause learning:

- 2-watched literals, 1-UIP learning, non-chronological backjump
- VSIDS activity heap, phase saving, restarts
- LBD-aware reduce, local conflict minimization, clause compact
- Multi-shot incremental API + assumption decisions
- Optional RUP/DRAT-style proof logging

### Assumptions and cores

```zig
const r = try solver.solveAssumptions(&.{ lit_a.not(), lit_b.not() });
// r.assumption_core: deletion-minimal subset (owned i32 DIMACS lits)
// r.assumption_core_unique: true iff this is the unique MUS of the set
```

A core is the **unique MUS** of assumption set *A* when it is a MUS and
∀a∈MUS. *A*\\{a} is SAT. When several MUSes exist, `unique` is false and the
returned core is still deletion-minimal.

## PDR / IC3 (`circuit/pdr.zig`)

Property-directed reachability for \(G(\neg\mathrm{bad})\):

- Frame clauses F[0]…F[k] with relative inductiveness checks
- MIC-style generalization + CTG predecessor blocking
- Ternary (0/1/X) pre-weakening of latch cubes
- Recursive `blockCube` obligations
- Push-to-quiescence and **clause-set** fixed-point detection
- Multi-property: `checkMulti` ORs all bad nets; empty bads → proven
- Resource caps: block-iteration limit, per-call `max_conflicts` (unknown ≠ hang)

## BMC & k-induction

- **BMC**: unroll *k* frames; OR of bad over time; constraints as units per frame.
- Multi-property `checkMulti`; empty bads → `safe_up_to_bound`.
- Init×constraint conflict ⇒ no legal path ⇒ vacuous safe (not violated).
- **k-induction**: base safety for 0…*k* plus step \(\neg\mathrm{bad}^{0..k-1} \land T^k \land \mathrm{bad}^k\) unsat.

## ABC delta (`bridge/abc_interop.zig`)

- Soft path: missing ABC → `abc_skip` (not a hard fail).
- `deltaLabel` matrix unit-tested without ABC.
- CLI: `logic-zig abc-delta <aig>`; multi-bad uses `mcSafetyMulti` (OR of props).

## Justice & k-Liveness

| Mode | Meaning |
|------|---------|
| Path justice | Finite path hits each justice ≥ once. |
| Lasso | Stem/end latch equality + justice/fairness on the loop. |
| k-Liveness | Infinite proof that justice cannot hold i.o. |

## Ternary simulation (`circuit/ternary.zig`)

Kleene 0/1/X evaluation for cube weakening and next-state steps under free inputs (X).

## External differential

`sat/external.zig` can invoke CaDiCaL (path discovery or
`LOGIC_ZIG_EXTERNAL_SOLVER`) for random CNF agreement checks.
