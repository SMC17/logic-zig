# Changelog

All notable changes to **logic-zig** are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project aims to follow [Semantic Versioning](https://semver.org/).

## [0.12.1] — 2026-07-16

### Added

- AIGER golden fixtures + `corpus/golden/manifest.jsonl` (safe/unsafe/lasso/klive/parse)
- `golden.runAll` = builtin + manifest + external DRAT-trim when present
- Portfolio: 6 configs, ramp budgets, model validation, optional RUP proof on UNSAT
- Fair multi-justice cases: dual lasso, fairness+stuck, three-signal one-dead
- `logic-sat check-drat` / `portfolio --proof` with external drat-trim verification

## [0.12.0] — 2026-07-16

### Added

- **Core + spin-off product matrix**: `logic` library + six flagship CLIs with named profiles.
- **Tier A:** GitHub Actions CI, golden suite (`logic-hwmcc golden`), products docs.
- **Tier B:** `cert/certificate` (k-liveness certs, inductive verify), minimal **BTOR2** reader.
- **Tier C:** sequential **portfolio** SAT, **bounded CTL** (EF/EG/AF/AG/fair-EG), **BV SMT-lite**, ABC path discovery.
- Profiles: `core`, `agent`, `sat-race`, `hwmcc`, `cert`, `smt`, `ctl`.

### Spin-offs

| Binary | Profile |
|--------|---------|
| `logic-agent` | agent |
| `logic-sat` | sat-race |
| `logic-hwmcc` | hwmcc |
| `logic-cert` | cert |
| `logic-smt` | smt |
| `logic-ctl` | ctl |

## [0.11.0] — 2026-07-16

### Added

- **Fair multi-justice completeness** via round-robin k-liveness over justice ∥ fairness.
- **Unique MUS** flag on assumption cores (`assumption_core_unique` / `extractAssumptionMus`).
- Gate kinds **nand / nor / xnor** end-to-end (CNF blast, ternary, Yosys, AIGER lower).
- Shared `circuit/blast.zig` for consistent sequential encodings.
- IC3a-oriented PDR stats: obligations, ternary drops; expanded engine docs.

### Changed

- Multi-justice proofs no longer rely only on single FG(¬J_i); use complete fair cycle measure.
- AIGER writer lowers the full gate set with structural hashing.

## [0.10.0] — 2026-07-16

### Added

- **k-Liveness** (`circuit/kliveness.zig`): infinite-trace proofs that a justice
  signal can hold only finitely often, via thermometer counters + k-induction/PDR.
- **Competition-style PDR**: recursive cube blocking, multi-round push to
  quiescence, clause-set fixed-point detection, lemma lift toward F[0].
- **Deletion-minimal assumption cores** with hard trail reset between probes;
  `isDeletionMinimalCore` verifier.
- **Structural hash-consing** in the AIGER writer (AND sharing + constant folding).
- CLI: `klive-demo`, `doctor`, HWMCC `--justice` / `--lasso` / extended flags.

### Changed

- BMC honors invariant constraints and multi-bad OR queries.
- HWMCC track uses `badProps()` (extended AIGER B section).
- Documentation rewritten for public release.

### Residual (honest)

- Multi-justice k-liveness is sound but incomplete (proves via any FG(¬J_i)).
- Unique MUS is undecidable in general; we guarantee **deletion-minimality**.
- AIGER is AND-Inverter only; OR/XOR/MUX still lower, with sharing to limit blow-up.

## [0.9.0] — 2026-07-16

Extended AIGER B/C/J/F, justice lasso encoding, ternary sim, AIGER writer.

## [0.1.0] — 2026-07-16

Initial public substrate: CDCL, Tseitin, BMC, k-induction, PDR, FOL, IPASIR.
