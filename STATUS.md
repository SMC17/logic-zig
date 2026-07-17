# logic-zig status

**Version:** 0.11.0  
**Last green:** 2026-07-16 — `zig build test` · `zig build` · `logic-zig doctor`

Proof level: **`unit-tested`**. Optional multi-axis **`benchmarked`** when CaDiCaL
and corpora are present (`win-report`, bench suites). Not a SAT Race entry.

## Component matrix (v0.11)

| Component | Level | Notes |
|-----------|-------|-------|
| CDCL + VSIDS/LBD/minimize/compact | `unit-tested` | Fuzz vs brute on small CNFs |
| Multi-shot + assumption cores | `unit-tested` | Deletion-minimal + **unique MUS** flag |
| RUP/DRAT log | `unit-tested` | Addition + deletion lines |
| IPASIR (Zig + `.so`) | `unit-tested` | |
| BMC multi-bad + constraints | `unit-tested` | |
| k-induction | `unit-tested` | |
| PDR (MIC/CTG/ternary/block/push FP) | `unit-tested` | IC3a-oriented; not full ABC binary |
| Justice path + lasso | `unit-tested` | |
| **k-Liveness + fair multi (round-robin)** | `unit-tested` | Complete reduction to safety |
| Ternary 0/1/X | `unit-tested` | |
| AIGER B/C/J/F + full gate lower | `unit-tested` | OR/XOR/MUX/NAND/NOR/XNOR + hash-cons |
| FOL / tracks | `unit-tested` | |

## Win scoreboard (when run)

Optional: `./zig-out/bin/logic-zig win-report` — PAR-2 / multishot / HWMCC micro vs CaDiCaL
when the external solver is available. Correctness is the hard gate.

## Residuals (honest)

1. **Unique MUS** — detected when unique; otherwise one minimal core with `unique=false`.
2. **Fair multi-justice** — complete *relative to* kind/PDR on the round-robin netlist; resource-bounded in *k*.
3. **ABC binary parity** — no fraig / localization / full ABC command suite.
4. **CTL operators** — fair EG-style justice/fairness covered; no separate AU/EU frontend.
5. **SAT Race industrial hardness** — not claimed.

## Smoke

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig klive-demo --max-k 4
./zig-out/bin/logic-zig pdr-demo
```
