# logic-zig

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Zig](https://img.shields.io/badge/Zig-0.16-orange.svg)](https://ziglang.org/)
[![CI](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml/badge.svg)](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml)
[![Version](https://img.shields.io/badge/version-0.21.0-green.svg)](STATUS.md)

**Universal logic library in pure Zig** — industrial SAT/MC kernels plus a living
taxonomy of named systems (classical, constructive, modal, fuzzy, probabilistic,
description logics, abduction, …). Maturity is tracked honestly; empty cells are
visible, not hidden.

| Pillar | What ships |
|--------|------------|
| **Computational core** | CDCL SAT, IPASIR, BMC / k-induction / PDR, k-liveness, RUP/DRAT |
| **Formal deduction** | Natural deduction, LK sequents, focusing search, automated proof search |
| **Non-classical** | Intuitionistic Kripke, linear ILL, fuzzy t-norms, paraconsistent LP |
| **Modal / agency** | Modal K, multi-agent epistemic Kᵢ, deontic O/P |
| **Abduction / induction** | Exhaustive, industrial, and complete MUS-based abduction; induction schemas |
| **KR / probabilistic** | ALC + SHIQ spines, independence + Markov logic networks |
| **Historical** | Aristotelian syllogistic (24 valid moods) |
| **Giants** | Optional CaDiCaL / Kissat / Z3 / ABC / Vampire discovery |

Proof posture: [`STATUS.md`](STATUS.md). Universal destination: [`docs/UNIVERSAL.md`](docs/UNIVERSAL.md).
Dependency graph: [`GRAPH.md`](GRAPH.md).

---

## Quick start

```sh
# Requires Zig 0.16
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build

./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig taxonomy    # named systems × maturity
./zig-out/bin/logic-zig giants      # discover external provers
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig api-info
```

Flagship spin-offs (each pins a tradeoff profile):

```sh
./zig-out/bin/logic-agent profile
./zig-out/bin/logic-sat profile
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-cert suite
./zig-out/bin/logic-smt demo-add
./zig-out/bin/logic-ctl demo
```

Product matrix: [`docs/PRODUCTS.md`](docs/PRODUCTS.md).

---

## Maturity ladder

Every named system in the registry carries an explicit level:

| Level | Meaning |
|-------|---------|
| `documented` | Named only |
| `skeleton` | Types/API link; may return unsupported |
| `fragment` | Real algorithms on a decidable slice |
| `engine` | Production path inside logic-zig |
| `industrial` | Scoreboard evidence vs external peer |
| `external` | Delegated to a giant via adapter |

```sh
./zig-out/bin/logic-zig taxonomy
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

Add via `build.zig.zon` / `b.dependency`, or vendor `src/` and import the `logic` module.

---

## Module map (v0.21)

| Path | Role |
|------|------|
| `src/sat/` | CDCL, preprocess, portfolio, DRAT, IPASIR |
| `src/circuit/` | Netlist, BMC, k-induction, PDR, justice, k-liveness |
| `src/fol/` | Terms, unify, finite models, resolution |
| `src/smt/` | BV, EUF, arrays |
| `src/deductive/` | Natural deduction, sequents, search, focusing |
| `src/abductive/` | Exhaustive, industrial, MUS-complete abduction |
| `src/inductive/` | Mathematical induction schemas + datatypes |
| `src/constructive/` | Intuitionistic Kripke |
| `src/substructural/` | Linear logic ILL |
| `src/modal/` | Kripke K, epistemic/deontic |
| `src/fuzzy/` | Gödel / product / Łukasiewicz + Kleene |
| `src/paraconsistent/` | Belnap-Dunn / LP |
| `src/probabilistic/` | Independence + Markov logic |
| `src/description/` | ALC + SHIQ |
| `src/historical/` | Aristotelian syllogistic |
| `src/nonmonotonic/` | Reiter default logic |
| `src/taxonomy/` | Living registry |
| `src/bridge/` | DIMACS, AIGER, giants discovery |

---

## Documentation

| Document | Contents |
|----------|----------|
| [STATUS.md](STATUS.md) | Version, platform table, residuals |
| [GRAPH.md](GRAPH.md) | Upstream / downstream dependency graph |
| [docs/UNIVERSAL.md](docs/UNIVERSAL.md) | North star + non-fiction rules |
| [docs/TAXONOMY_COVERAGE.md](docs/TAXONOMY_COVERAGE.md) | Honest coverage map |
| [docs/INDUSTRIAL.md](docs/INDUSTRIAL.md) | SAT/MC/SMT/FOL depth program |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Layered design |
| [docs/ENGINES.md](docs/ENGINES.md) | Engine contracts |
| [docs/PRODUCTS.md](docs/PRODUCTS.md) | Spin-off product matrix |
| [CHANGELOG.md](CHANGELOG.md) | Version history |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to contribute |
| [SECURITY.md](SECURITY.md) | Vulnerability reporting |
| [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) | Community standards |
| [LICENSE](LICENSE) | Apache-2.0 |

---

## Correctness posture

We prefer **narrow, testable contracts** over marketing language:

- SAT models validate on the CNF; prop models re-evaluate on the AST.
- Assumption cores are deletion-minimal.
- Registry maturity is raised only when code + tests land in the same change.
- Fair k-liveness `proven_infinite` is complete relative to the safety engine on the round-robin reduction.
- External parity (Kissat, Z3, Vampire, …) is **never claimed** without scoreboard evidence.

Known residuals live in [`STATUS.md`](STATUS.md).

---

## License

Copyright contributors to logic-zig.  
Licensed under the [Apache License, Version 2.0](LICENSE).
