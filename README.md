# logic-zig

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Zig](https://img.shields.io/badge/Zig-0.16-orange.svg)](https://ziglang.org/)

**A Zig-native logic kernel** for SAT solving, sequential model checking, and
lightweight first-order reasoning — designed for correctness contracts you can
actually audit.

| | |
|---|---|
| **SAT** | CDCL with VSIDS, LBD reduce, multi-shot assumptions, RUP/DRAT, IPASIR |
| **Hardware / sequential** | Netlists, AIGER (extended B/C/J/F), Yosys JSON, BMC, k-induction, PDR |
| **Liveness** | Justice path/lasso witnesses **and** k-liveness infinite-trace proofs |
| **FOL** | Unification + finite-domain model finding (brute and SAT-encoded) |

Proof posture is documented in [`STATUS.md`](STATUS.md): features are marked
`unit-tested` or residual — no silent overclaims.

---

## Quick start

```sh
# Requires Zig 0.16
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build

./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig sat 'a & (a -> b)'
./zig-out/bin/logic-zig sat --file corpus/simple_unsat.cnf --proof
./zig-out/bin/logic-zig pdr-demo
./zig-out/bin/logic-zig klive-demo --max-k 4
```

Optional differential oracle ([CaDiCaL](https://github.com/arminbiere/cadical)):

```sh
git clone https://github.com/arminbiere/cadical.git third_party/cadical
( cd third_party/cadical && ./configure && make -j"$(nproc)" )
# or: export LOGIC_ZIG_EXTERNAL_SOLVER=/path/to/cadical
./zig-out/bin/logic-zig diff-external --iters 20
```

---

## Features

### CDCL SAT

- 2-watched literals, 1-UIP learning, non-chronological backjump
- Heap VSIDS, phase saving, restarts, LBD-aware clause database reduce
- Conflict clause minimization and learned-clause compact
- Multi-shot incremental solving + **deletion-minimal assumption cores**
- RUP verification path for unsat proofs
- C ABI via **IPASIR** (`libipasirlogic.so`, `include/ipasir.h`)

### Sequential model checking

| Engine | Use |
|--------|-----|
| **BMC** | Bounded reachability of bad (multi-property, constraints) |
| **k-induction** | Inductive safety proofs |
| **PDR / IC3** | MIC + CTG + ternary weakening, recursive blocking, fixed points |
| **Justice** | Bounded path / lasso fair witnesses |
| **k-Liveness** | Thermometer reduction → **infinite** “justice only finitely often” proofs |

### Circuits & interchange

- Netlist IR: AND/OR/XOR/NOT/MUX/const, latches, bad/constraint/justice/fairness
- **AIGER** ASCII/binary reader (classic + extended headers, symbols)
- **AIGER writer** with structural hash-consing and constant folding
- Yosys JSON import (combinational cells + `$dff`)

### Competition-style tracks

```sh
./zig-out/bin/logic-zig sat-track instance.cnf
./zig-out/bin/logic-zig hwmcc-track design.aag --frames 16
./zig-out/bin/logic-zig hwmcc-track design.aag --justice --lasso --frames 16
```

---

## Library usage

```zig
const std = @import("std");
const logic = @import("logic");

pub fn main() !void {
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    defer _ = gpa.deinit();
    const a = gpa.allocator();

    var pool = try logic.ExprPool.init(a);
    defer pool.deinit();

    const e = try logic.parse(&pool, "(a -> b) & a & !b");
    const q = try logic.satFormula(a, &pool, e);
    defer if (q.model) |m| a.free(m);

    std.debug.print("{s}\n", .{@tagName(q.status)}); // unsat
}
```

Add as a dependency via `build.zig.zon` / `b.dependency` pointing at this repo,
or vendor `src/` and import the `logic` module as in this tree’s `build.zig`.

---

## Architecture

```
prop ──► ExprPool ──Tseitin──► CNF ──► CDCL ──► model / RUP / cores
                              multi-shot · IPASIR · Δ CaDiCaL

AIGER / Yosys ──► Netlist ──► BMC · k-induction · PDR
                     │         justice (path/lasso) · k-liveness
                     └──► AIGER writer (hash-consed AIG)

FOL ── unify · finite models (enumerate / SAT)
```

See [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) and [docs/ENGINES.md](docs/ENGINES.md).

---

## Documentation

| Document | Contents |
|----------|----------|
| [STATUS.md](STATUS.md) | Proof levels, green checklist, residuals |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Layered design |
| [docs/ENGINES.md](docs/ENGINES.md) | Engine contracts |
| [CHANGELOG.md](CHANGELOG.md) | Version history |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to hack on the tree |
| [LICENSE](LICENSE) | Apache-2.0 |

---

## CLI overview

```text
logic-zig sat <formula | --file f.cnf> [--proof]
logic-zig sat-track <f.cnf>
logic-zig hwmcc-track <f.aag|aig> [--frames N] [--each] [--justice] [--lasso]
logic-zig fuzz · miter · unify · eval · cnf · tautology · equiv
logic-zig bmc-demo · kind-demo · pdr-demo · justice-demo · klive-demo
logic-zig aiger · aiger-write [--binary] [--extended]
logic-zig doctor · diff-external · bench-suite · correctness-suite
```

---

## Correctness posture

We prefer **narrow, testable contracts** over marketing language:

- SAT models validate on the CNF; prop models re-evaluate on the AST.
- Assumption cores are **deletion-minimal** (local MUSes), not unique MUSes.
- k-Liveness `proven_infinite` means a thermometer safety proof at some *k*.
- PDR `proven` means an inductive frame fixed point was found — not “ABC parity.”

Known residuals are listed in [`STATUS.md`](STATUS.md).

---

## License

Copyright contributors to logic-zig.  
Licensed under the [Apache License, Version 2.0](LICENSE).
