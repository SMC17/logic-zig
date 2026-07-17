# Architecture

**logic-zig** is a Zig 0.16 library and CLI for propositional SAT, sequential
model checking, and lightweight first-order reasoning. This note describes the
data path from formula / circuit input to certificates and counterexamples.

## Layers

```
┌─────────────────────────────────────────────────────────────┐
│ CLI (sat, tracks, demos, doctor)                            │
├─────────────────────────────────────────────────────────────┤
│ Tracks: sat-track · hwmcc-track · benches                   │
├──────────────┬──────────────────────────┬───────────────────┤
│ Prop IR      │ Sequential engines       │ FOL               │
│ ExprPool     │ BMC · k-ind · PDR        │ unify · models    │
│ Tseitin      │ justice · k-liveness     │                   │
├──────────────┴──────────────────────────┴───────────────────┤
│ CDCL kernel (2WL, 1-UIP, VSIDS, LBD, minimize, compact)     │
│ multi-shot · assumptions · deletion-minimal cores · DRAT    │
├─────────────────────────────────────────────────────────────┤
│ Frontends: DIMACS · AIGER aag/aig · Yosys JSON              │
└─────────────────────────────────────────────────────────────┘
```

## Propositional path

1. Parse text into a hash-consed `ExprPool` (`ir/expr.zig`).
2. Optional NNF / simplify.
3. Tseitin transform → `Cnf` (`pass/tseitin.zig`).
4. CDCL solve (`sat/solver.zig`); optional RUP/DRAT proof log.
5. Models are checked against the original CNF; prop models are re-evaluated on
   the expression DAG.

## Sequential path

Netlists (`circuit/netlist.zig`) hold gates, latches, and HWMCC-style property
lists (`bad`, `constraints`, `justice`, `fairness`).

| Engine | Claim |
|--------|--------|
| **BMC** | Reachability of bad within bound *k* (under constraints). |
| **k-induction** | Base BMC + inductive step ⇒ safety for all time. |
| **PDR / IC3** | Frame sequence + MIC/CTG/ternary gen; fixed point ⇒ safety. |
| **Justice path/lasso** | Bounded (or cyclic) witness that justice holds often enough. |
| **k-Liveness** | Thermometer counter + safety proof ⇒ justice only finitely often (**infinite-trace proof**). |

### k-Liveness sketch

For justice signal *J*, introduce thermometer latches \(t_0,\ldots,t_k\):

\[
t_0' = t_0 \lor J,\quad
t_i' = t_i \lor (J \land t_{i-1}),\quad
\mathrm{bad} \equiv t_k.
\]

If \(G(\neg\mathrm{bad})\) is proven, then *J* holds at most *k* times on every
path from the initial states, hence only finitely often on every infinite path.
That refutes the existence of an infinite path where *J* is true infinitely often.

## AIGER

- **Reader** accepts classic `M I L O A` and extended `B C J F` headers (ASCII and binary).
- **Writer** lowers OR/XOR/MUX to the AIG basis (AND + inverter edges) with
  **structural hash-consing** and constant folding so shared subexpressions are
  not re-expanded.

## Correctness contracts

| Result | Guarantee |
|--------|-----------|
| SAT model | Satisfies original CNF (`Cnf.checkModel`). |
| UNSAT + proof | RUP-checked clause additions (optional). |
| Assumption core | **Deletion-minimal** over the assumption set (local MUS). |
| PDR `proven` | Inductive invariant found (frame fixed point). |
| k-Liveness `proven_infinite` | Safety of thermometer at some *k*. |

## Non-goals (current)

- Full competition IC3a / ABC feature parity.
- Unique MUS extraction when multiple MUSes exist.
- Complete multi-justice fair-CTL without reducing via single FG(¬J_i).
