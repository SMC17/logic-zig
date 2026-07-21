# Contributing to logic-zig

Thank you for interest in improving **logic-zig**. This document is the short path
from clone → green tests → a reviewable change.

## Prerequisites

- [Zig](https://ziglang.org/) **0.16.x** (the version this tree is developed against)
- Optional: [Lean](https://lean-lang.org/) via `elan`; the oracle project pins its
  own toolchain in `lean/lean-toolchain`
- Optional: [CaDiCaL](https://github.com/arminbiere/cadical) for differential SAT checks

```sh
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build
./zig-out/bin/logic-zig doctor
( cd lean && lake build )
```

## Project rules

1. **Evidence first.** Prefer a failing test before a fix. Load-bearing claims should
   be unit-tested or clearly marked as sketch / residual in `STATUS.md`.
2. **Narrow diffs.** Touch only modules needed for the change.
3. **Zig 0.16 APIs.** Use `ArrayList = .empty`, `std.process.Init`, `Io.Writer.Allocating`,
   etc. Do not reintroduce removed 0.13/0.14 patterns.
4. **No secrets.** Never commit wallet addresses, tokens, or private workstation paths.
5. **Honest residuals.** If a feature is incomplete (e.g. multi-justice completeness),
   document it in `STATUS.md` rather than over-claiming.
6. **Generated proofs are untrusted.** Aristotle or any other prover may propose
   Lean code, but PRs must preserve theorem statements and pass the pinned Lean
   build without proof placeholders, custom axioms, or unsafe escapes.

## Layout

| Path | Role |
|------|------|
| `src/sat/` | CDCL, DRAT, IPASIR, external solvers |
| `src/circuit/` | Netlist, BMC, k-induction, PDR, justice, k-liveness, ternary |
| `src/bridge/` | DIMACS, AIGER read/write |
| `src/fol/` | Terms, unification, finite models |
| `src/track/` | SAT / HWMCC competition front-ends |
| `corpus/` | Small CNF / AIGER / Yosys fixtures |
| `tests/` | Integration tests |
| `lean/` | Kernel-checked semantic oracle contracts |

## Submitting changes

1. Branch from `main`.
2. `zig build test` must pass.
3. Add or update unit tests next to the module you change.
4. Update `CHANGELOG.md` under `[Unreleased]` if the change is user-visible.
5. Open a PR with a short problem statement and proof level (`unit-tested` / `sketch`).

Use the structured issue forms for correctness defects and new exhibits. Report
proof-verification bypasses privately as described in `SECURITY.md`.

## Coding style

- Module-level `//!` docs for public engines.
- Prefer explicit error sets and `defer` for owned resources.
- Avoid silent `catch {}` on correctness paths.

## License

By contributing, you agree that your contributions are licensed under the
**Apache License 2.0** (see [`LICENSE`](LICENSE)).
