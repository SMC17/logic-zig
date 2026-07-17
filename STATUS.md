# Status

**Version:** 0.10.0  
**Last green:** 2026-07-16 — `zig build test` · `zig build` · `logic-zig doctor`

## Proof levels

| Level | Meaning |
|-------|---------|
| `unit-tested` | Covered by automated tests in-tree; claim holds on those cases. |
| `sketch` | Implemented path exists; not claimed complete / competition-complete. |
| `residual` | Documented gap; do not claim. |

## Component matrix

| Component | Level | Notes |
|-----------|-------|-------|
| CDCL + VSIDS/LBD/minimize/compact | `unit-tested` | Fuzz vs brute on small CNFs |
| Multi-shot + assumption cores | `unit-tested` | Deletion-minimal cores + verifier |
| RUP/DRAT log | `unit-tested` | Addition + deletion lines |
| IPASIR (Zig + `.so`) | `unit-tested` | Failed-lit after unsat under assumptions |
| External CaDiCaL Δ | `unit-tested` | When solver present |
| BMC multi-bad + constraints | `unit-tested` | |
| k-induction | `unit-tested` | Stuck-0 proven; counter violated |
| PDR (MIC/CTG/ternary/block/push FP) | `unit-tested` | Not full IC3a feature parity |
| Justice path + lasso | `unit-tested` | Bounded witnesses |
| **k-Liveness infinite proof** | `unit-tested` | Thermometer + kind/PDR |
| Ternary 0/1/X | `unit-tested` | |
| AIGER read B/C/J/F | `unit-tested` | ASCII + binary |
| AIGER write + hash-cons | `unit-tested` | AND basis; shared ANDs |
| FOL unify / finite models | `unit-tested` | |
| SAT / HWMCC tracks | `unit-tested` | |

## Residuals (explicit)

1. **Unique MUS** — not unique in general; we guarantee deletion-minimality only.
2. **Multi-justice completeness** — k-liveness proves via any single FG(¬J_i) (sound, incomplete for some multi-fair specs).
3. **PDR competition parity** — no full ternary simulation lattice over all CTG cases, no ABC-scale engineering.
4. **AIGER basis** — OR/XOR/MUX lower to AND+NOT by definition of AIG; mitigated by hash-cons + folding.
5. **k-Liveness** — complete for single-signal “finitely often” when the safety engine proves the thermometer; resource-bounded in *k* and PDR frames.

## Smoke

```sh
zig build test && zig build && ./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig klive-demo --max-k 4
./zig-out/bin/logic-zig pdr-demo
```
