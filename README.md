# logic-zig

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Zig](https://img.shields.io/badge/Zig-0.16-orange.svg)](https://ziglang.org/)
[![CI](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml/badge.svg)](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml)

**An executable museum and comparative laboratory of logic in Zig.** Each named
system is intended to receive an explicit syntax, semantics, proof theory,
automation boundary, test corpus, and checkable evidence. The current SAT and
model-checking spine supports that expansion; exhibit maturity is derived rather
than implied by catalog breadth.

| | |
|---|---|
| **SAT** | CDCL with VSIDS, LBD reduce, multi-shot assumptions, RUP/DRAT, IPASIR |
| **Hardware / sequential** | Netlists, AIGER (extended B/C/J/F), Yosys JSON, BMC, k-induction, PDR |
| **Liveness** | Justice path/lasso + **fair multi-justice** round-robin k-liveness (complete reduction) |
| **FOL** | Unification + finite-domain model finding (brute and SAT-encoded) |
| **Reasoning modes** | Deduction (SAT/SMT/FOL oracle) · **abduction** (subset-minimal + min-cost via MaxSAT, first-order ALP) · **induction** (minimal-k DNF synthesis, exact Bayesian posterior) — the Peircean triad as engines |
| **Nonmonotonic** | Reiter defaults · KLM rational closure · ASP stable models · circumscription · Dung argumentation · AGM belief revision |
| **Analogical** | Boolean analogical proportions (axioms verified), proportion solving, abstaining analogical classifier |
| **Non-classical** | Intuitionistic (G4ip decision, Glivenko-verified) · many-valued matrices (K3/LP/FDE/Ł3) · multi-agent epistemic S5 with common knowledge & announcements |
| **Classical roots** | Complete Aristotelian syllogistic decision (15/24 of 256 forms) · description logic EL subsumption |
| **Substructural & normative** | MLL linear logic prover (weakening/contraction refuted) · deontic SDL (D ⇔ seriality) |
| **Optimization** | Weighted partial MaxSAT (exact, brute-force-verified) powering cost-ranked explanations |

Proof posture is documented in [`STATUS.md`](STATUS.md): features are marked
`unit-tested` or residual — no silent overclaims.

---

## Quick start

```sh
# Requires Zig 0.16
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build   # umbrella + spin-offs + libipasirlogic.so

./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig api-info   # stable api/v1 + industrial capability matrix
./zig-out/bin/logic-zig taxonomy   # universal named-systems registry
./zig-out/bin/logic-zig museum     # evidence-derived exhibit contracts
./zig-out/bin/logic-zig check-rup formula.cnf proof.rup
./zig-out/bin/logic-zig giants     # discover external industrial provers
./zig-out/bin/logic-hwmcc golden

# Flagship spin-offs (each pins a unique tradeoff profile)
./zig-out/bin/logic-agent profile
./zig-out/bin/logic-sat profile
./zig-out/bin/logic-hwmcc profile
./zig-out/bin/logic-cert klive-demo
./zig-out/bin/logic-smt demo-add
./zig-out/bin/logic-ctl demo
```

Product matrix and profiles: **[docs/PRODUCTS.md](docs/PRODUCTS.md)**.

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
| [docs/MUSEUM.md](docs/MUSEUM.md) | Exhibit contracts and promotion gates |
| [docs/exhibits/prop-classical.md](docs/exhibits/prop-classical.md) | Verified classical propositional exhibit |
| [docs/exhibits/syllogistic.md](docs/exhibits/syllogistic.md) | Verified categorical syllogistic exhibit |
| [docs/exhibits/finite-matrices.md](docs/exhibits/finite-matrices.md) | Verified K3, LP, FDE, and L3 exhibits |
| [CHANGELOG.md](CHANGELOG.md) | Version history |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to hack on the tree |
| [LICENSE](LICENSE) | Apache-2.0 |

---

## CLI overview

```text
logic-zig sat <formula | --file f.cnf> [--proof]
logic-zig sat-track <f.cnf> [--max-conflicts N] [--portfolio] [--proof] [--quiet]
logic-zig hwmcc-track <f.aag|aig> [--frames N] [--each] [--justice] [--lasso] [--cert] [--no-kind]
logic-zig fuzz · miter · unify · eval · cnf · tautology · equiv
logic-zig bmc-demo · kind-demo · pdr-demo · justice-demo · klive-demo
logic-zig aiger · aiger-write [--binary] [--extended]
logic-zig doctor · diff-external · bench-suite · correctness-suite
```

---

## Correctness posture

We prefer **narrow, testable contracts** over marketing language:

- SAT models validate on the CNF; prop models re-evaluate on the AST.
- Assumption cores are deletion-minimal; `assumption_core_unique` marks a **unique MUS**.
- Fair k-liveness `proven_infinite` is complete relative to the safety engine on the round-robin reduction.
- PDR `proven` means an inductive frame fixed point (IC3a-oriented feature set, not full ABC).

Known residuals are listed in [`STATUS.md`](STATUS.md).

---

## License

Copyright contributors to logic-zig.  
Licensed under the [Apache License, Version 2.0](LICENSE).
