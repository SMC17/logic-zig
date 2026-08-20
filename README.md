# logic-zig

[![License](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](LICENSE)
[![Zig](https://img.shields.io/badge/Zig-0.16-orange.svg)](https://ziglang.org/)
[![CI](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml/badge.svg)](https://github.com/SMC17/logic-zig/actions/workflows/ci.yml)
[![Version](https://img.shields.io/badge/version-0.24.0-green.svg)](STATUS.md)

**An executable museum of logic, and a kernel for agent-trust — in Zig.**

This is not another SAT solver. CDCL, model checking, and certificates are the
substrate. The product is named logical systems with explicit contracts,
checkable evidence, and fail-closed trust.

Built for:

- **Agent platforms** that must *check* reasoning — incremental SAT, deletion-minimal
  cores, RUP/DRAT proofs, inductive safety certificates, stable `api/v1`.
- **Lean / Zig tooling** — fast Zig engines next to a documented Lean semantic-oracle
  contract. A kernel-checked Lean project is a named residual, not a README claim.

| Surface | What ships on `main` |
|---------|----------------------|
| **Trust kernel** | CDCL, IPASIR, BMC / k-induction / PDR, k-liveness, RUP/DRAT, `trust-report` |
| **Museum spine** | Taxonomy of named systems × maturity; fragments stay fragments |
| **Agent surface** | `logic-agent` multishot profile, assumption cores, `api/v1` |
| **Lean oracle** | Contract + Zig fixture schema in [`docs/LEAN_ORACLE.md`](docs/LEAN_ORACLE.md) |

Proof posture: [`STATUS.md`](STATUS.md). Non-fiction rules: [`docs/UNIVERSAL.md`](docs/UNIVERSAL.md).
Graph: [`GRAPH.md`](GRAPH.md).

---

## 90 seconds

```sh
# Requires Zig 0.16
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build

./zig-out/bin/logic-zig doctor      # smoke: prop, CDCL, AIGER, PDR, k-liveness
./zig-out/bin/logic-zig taxonomy    # named systems × maturity (the museum index)
./zig-out/bin/logic-zig api-info    # stable api/v1 + capability bits
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-agent profile
```

`trust-report` is fail-closed: missing CaDiCaL, DRAT-trim, or ABC is reported and
blocks `TRUST_OK`. That is the intended agent-trust behavior, not a silent skip.

Step-by-step: [`docs/GETTING_STARTED.md`](docs/GETTING_STARTED.md).
Product matrix: [`docs/PRODUCTS.md`](docs/PRODUCTS.md).

```sh
./zig-out/bin/logic-sat profile
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-cert suite
./zig-out/bin/logic-smt demo-add
./zig-out/bin/logic-ctl demo
./zig-out/bin/logic-zig giants      # discover optional Kissat/Z3/ABC/Vampire/…
```

---

## Who this is for

### Agent platforms that need checkable reasoning

`logic-agent` pins the incremental / assumption-heavy profile. Integrate through
`@import("logic").api` rather than scraping CLI output:

```zig
const api = @import("logic").api;
// api.version_string, api.Capability.current()
// api.satDimacs(allocator, src, .{ .preprocess = true })
// api.mcAiger(allocator, aig_src, .{ .cert = true })
```

Checkable artifacts on this tree: SAT models re-eval on the CNF, deletion-minimal
assumption cores, RUP/DRAT unsat proofs, PDR inductive invariants, k-liveness
certificates. See [`docs/TRUST.md`](docs/TRUST.md) and [`docs/PRODUCTS.md`](docs/PRODUCTS.md).

### Lean / Zig tooling

Zig owns IR, search, resource behavior, and replay. Lean is the external
semantic oracle, not a substitute implementation. The in-tree contract and
many-valued fixture schema live in [`docs/LEAN_ORACLE.md`](docs/LEAN_ORACLE.md).
Kernel-checked Lean (`lake build`, no `sorry`/`axiom` escapes) and Zig↔Lean
differential replay are tracked as issues [#3](https://github.com/SMC17/logic-zig/issues/3)
and [#6](https://github.com/SMC17/logic-zig/issues/6); they are not claimed on
this README.

---

## What this is not

- **Not a SAT-race bid.** Kissat / CaDiCaL / ABC / Z3 / Vampire parity is never
  claimed without a scoreboard. Giants are discovered, not reimplemented first.
- **Not a completed museum.** Registry breadth is an index. Completeness is local
  to a named system and its evidence. Fail-closed exhibit CLI work is a residual
  ([STATUS.md](STATUS.md)).
- **Not a new logic family this week.** New rows start at `documented`. Maturity
  rises only with code + tests in the same change.

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

## Module map (v0.24)

| Path | Role |
|------|------|
| `src/sat/` | CDCL, preprocess, portfolio, DRAT, IPASIR |
| `src/circuit/` | Netlist, BMC, k-induction, PDR, justice, k-liveness |
| `src/cert/` `src/trust/` | Certificates and fail-closed trust report |
| `src/agent/` | Multishot / assumption sessions |
| `src/api/` | Stable `api/v1` |
| `src/fol/` | Terms, unify, finite models, resolution |
| `src/smt/` | BV, EUF, arrays |
| `src/deductive/` | Natural deduction, sequents, search, focusing |
| `src/abductive/` | Exhaustive, industrial, MUS-complete abduction |
| `src/inductive/` | Mathematical induction schemas + datatypes |
| `src/constructive/` | Intuitionistic Kripke |
| `src/substructural/` | Linear ILL, relevance R fragment |
| `src/modal/` | Kripke K–S5, epistemic/deontic, traces |
| `src/fuzzy/` | Gödel / product / Łukasiewicz + Kleene |
| `src/paraconsistent/` | Belnap-Dunn / LP |
| `src/manyvalued/` | Lean-differential fixture schema |
| `src/probabilistic/` | Independence, Markov logic, WPLL |
| `src/description/` | ALC + SHIQ + pairwise blocking |
| `src/historical/` | Aristotelian syllogistic |
| `src/nonmonotonic/` | Reiter defaults, KLM |
| `src/type_theory/` | MLTT micro, HOL fragment, Huet |
| `src/algebraic/` | Categorical spine |
| `src/taxonomy/` | Living registry |
| `src/bridge/` | DIMACS, AIGER, giants discovery |

---

## Documentation

| Document | Contents |
|----------|----------|
| [STATUS.md](STATUS.md) | Version, platform table, residuals |
| [docs/GETTING_STARTED.md](docs/GETTING_STARTED.md) | Clone → doctor |
| [docs/TRUST.md](docs/TRUST.md) | Certificates and `TRUST_OK` gates |
| [docs/LEAN_ORACLE.md](docs/LEAN_ORACLE.md) | Lean oracle contract (kernel work is residual) |
| [docs/UNIVERSAL.md](docs/UNIVERSAL.md) | North star + non-fiction rules |
| [docs/TAXONOMY_COVERAGE.md](docs/TAXONOMY_COVERAGE.md) | Honest coverage map |
| [docs/PRODUCTS.md](docs/PRODUCTS.md) | Spin-off product matrix |
| [docs/INDUSTRIAL.md](docs/INDUSTRIAL.md) | SAT/MC/SMT/FOL depth program |
| [docs/ARCHITECTURE.md](docs/ARCHITECTURE.md) | Layered design |
| [docs/ENGINES.md](docs/ENGINES.md) | Engine contracts |
| [GRAPH.md](GRAPH.md) | Upstream / downstream dependency graph |
| [CHANGELOG.md](CHANGELOG.md) | Version history |
| [CONTRIBUTING.md](CONTRIBUTING.md) | How to contribute |
| [SECURITY.md](SECURITY.md) | Vulnerability reporting |
| [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) | Community standards |
| [LICENSE](LICENSE) | Apache-2.0 |

---

## Correctness posture

Narrow, testable contracts over marketing language:

- SAT models validate on the CNF; prop models re-evaluate on the AST.
- Assumption cores are deletion-minimal.
- Registry maturity is raised only when code + tests land in the same change.
- Fair k-liveness `proven_infinite` is complete relative to the safety engine on the round-robin reduction.
- External parity (Kissat, Z3, Vampire, …) is **never claimed** without scoreboard evidence.
- Lean output, including any Aristotle-generated proof, is untrusted until the
  pinned kernel builds it.

Known residuals live in [`STATUS.md`](STATUS.md).

---

## License

Copyright contributors to logic-zig.  
Licensed under the [Apache License, Version 2.0](LICENSE).
