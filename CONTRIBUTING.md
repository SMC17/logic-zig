# Contributing to logic-zig

Thank you for interest in improving **logic-zig**. Short path from clone → green
tests → a reviewable change.

## Prerequisites

- [Zig](https://ziglang.org/) **0.16.x**
- Optional: [CaDiCaL](https://github.com/arminbiere/cadical) for differential SAT checks

```sh
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig taxonomy
```

## Project rules

1. **Evidence first.** Prefer a failing test before a fix. Load-bearing claims
   must be unit-tested or clearly marked residual in `STATUS.md`.
2. **Registry honesty.** Raising a taxonomy row's maturity requires code + tests
   in the same change. Never mark `engine` / `industrial` without gates.
3. **Narrow diffs.** Touch only modules needed for the change.
4. **Zig 0.16 APIs.** Use `ArrayList = .empty`, `std.process.Init`, etc.
5. **No secrets.** Never commit tokens, private paths, or credentials.
6. **Non-fiction rule.** See `docs/UNIVERSAL.md` — no silent overclaims.

## Layout

| Path | Role |
|------|------|
| `src/sat/` | CDCL, DRAT, IPASIR, external solvers |
| `src/circuit/` | Netlist, BMC, k-induction, PDR, justice, k-liveness |
| `src/bridge/` | DIMACS, AIGER, giants |
| `src/fol/` | Terms, unification, finite models, resolution |
| `src/smt/` | BV, EUF, arrays |
| `src/deductive/` | ND, sequents, search, focusing |
| `src/abductive/` | Exhaustive / industrial / MUS abduction |
| `src/inductive/` | Induction schemas |
| `src/constructive/` | Intuitionistic |
| `src/substructural/` | Linear logic |
| `src/modal/` | Kripke, epistemic/deontic |
| `src/fuzzy/`, `src/paraconsistent/` | Many-valued |
| `src/probabilistic/` | Independence, Markov logic |
| `src/description/` | ALC, SHIQ |
| `src/historical/` | Syllogistic |
| `src/nonmonotonic/` | Default logic |
| `src/taxonomy/` | Living registry |
| `corpus/` | CNF / AIGER fixtures |

## Submitting changes

1. Branch from `main`.
2. `zig build test` must pass; run `doctor` and `taxonomy` for platform changes.
3. Co-locate unit tests in the module you change.
4. Update `CHANGELOG.md` under the next version section if user-visible.
5. If you add a named system, update `src/taxonomy/registry.zig` and
   `docs/TAXONOMY_COVERAGE.md` in the same PR.
6. Open a PR with problem statement + proof level (`unit-tested` / `fragment` / `sketch`).

## Coding style

- Module-level `//!` docs for public engines.
- Prefer explicit error sets and `defer` for owned resources.
- Avoid silent `catch {}` on correctness paths.
- Allocator-aware; no hidden globals.

## License

By contributing, you agree that your contributions are licensed under the
**Apache License 2.0** (see [`LICENSE`](LICENSE)).
