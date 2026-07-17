# Changelog

All notable changes to **logic-zig** are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project aims to follow [Semantic Versioning](https://semver.org/).

## [0.16.0] — 2026-07-16

### Industrial wave: vivify · sat_hard · UF · ABC path

- **Vivification** in preprocess (literal/clause strengthen via UP under ~others)
- **sat-scoreboard --industrial**: portfolio + vivify + higher timeout; `sat_hard` CI sample
- **SMT UF spine** (`smt/uf.zig`): congruence closure, diseq, unary preds; capability `smt_uf=true`
- **ABC path**: `abc-delta` compares internal MC vs ABC PDR when `abc` present
- Trust report: SMT UF checks
- Honest residual: PAR-2 vs CaDiCaL not guaranteed; full industrial parity not claimed

## [0.15.1] — 2026-07-16

### Industrial SAT Phase 1

- **Preprocess deep:** BCP fixpoint, pure-literal elim, unit self-subsuming resolution, subsumption
- **Inprocessing:** `SolverOptions.inprocess_interval` drops satisfied learned clauses
- **`solveCnf` preprocess flag** for one-shot industrial path
- **`logic-zig sat-scoreboard`**: frozen suite vs CaDiCaL — mismatches, PAR-2, instance speed
- CI: scoreboard on `sat` + `sat_comp` samples

## [0.15.0] — 2026-07-16

### Industrial program foundation

- **`docs/INDUSTRIAL.md`**: phased path to industrial SAT/MC, SMT, FOL, ABC-class, stable API
- **`src/api/v1.zig`**: stable contract — version `1.0.0`, `Capability` bits, `satCnf`/`satDimacs`, `mcSafety`/`mcAiger`
- **CLI `api-info`**: print version + feature matrix
- **SAT preprocess**: tautology-aware clean path, forward subsumption, dedup (`sat/preprocess.zig`)
- **SMT facade**: `SmtSolver` + theory enum (BV live; UF/array/UFBV → `unsupported` honestly)
- **FOL resolution**: given-clause resolution skeleton with unify (`fol/resolution.zig`)

### Residual

- Industrial *parity* not claimed; pillars mature per INDUSTRIAL.md phases

## [0.14.0] — 2026-07-16

### Competition + robustness

- **`sat-track`**: competition s/v output, exit codes 10/20/0, `--max-conflicts`,
  `--portfolio`, `--proof` (RUP gate before UNSAT claim), `--quiet`, model validation
- **Portfolio**: 9 sequential configs (pure-literal, no-min+rephase, glue-keep1, …)
- **DIMACS harden**: var/clause caps, reject garbage lines, empty formula, `%` section end
- **HWMCC track**: PDR → k-induction → BMC; CLI `--cert` / `--no-kind`
- **Designs**: one-hot ring, Johnson counter, dual-rail safe, parity-never-bad
- **`logic-cert suite`**: multi-design cert battery; **`designs-demo`** depth
- **Solver**: allocation failure is `OutOfMemory`, never reported as conflict/UNSAT
- **PDR**: bounded max_conflicts on init queries
- **CI**: sat-track competition smoke + cert suite
- Trust report: kind cert, one-hot, agent structured/stress counters

### Residual

- Not industrial SAT/HWMCC race parity; RUP-centric proofs; IPASIR callbacks partial

## [0.13.1] — 2026-07-16

### Climb

- Structured agent warm-cold (`--structured`) for related assumption refinements
- Designs: mutex + constraint, 5-bit counter teeth, multi-stuck5 certs
- HWMCC `--cert`: emit verified inductive invariant on proven
- `logic-hwmcc designs-demo`
- Trust report: sequential ok=6; golden **51/51**

## [0.13.0] — 2026-07-16

### Trust · Agent · Sequential teeth

- **`logic-zig trust-report`**: DRAT verified counts, CaDiCaL Δ, PDR cert re-check, sequential designs, klive
- **`designs.zig`**: n-bit counter, shift register, multi-stuck0, fair toggle products
- **Agent session**: stress (1000+ queries), warm-vs-cold, dimacs add/query, optional proofs
- **`ipasir-consumer` example** binary for external gravity
- Docs: `docs/TRUST.md`, `docs/AGENT.md`
- Golden **48/48** including design-based certs and agent stress micro

## [0.12.3] — 2026-07-16

### Added

- AIGER goldens: `hold_true`/`hold_false`, `dual_stuck`, `and2_bad_ext`
- Golden **44/44** (builtin expansion + fuller manifest)
- `logic-hwmcc fair-demo` + **`stack`** (golden + track stuck0)
- Doctor: fair multi, portfolio, drat-trim
- CI: sat_hard sample, hwmcc stack, track fixtures
- Builtin: counter BMC bounds, aag/aig write roundtrip, nand unsat

## [0.12.2] — 2026-07-16

### Added

- More AIGER goldens: `stuck0_b`, `init1_bad`, `const0_safe`, `toggle_justice`
- Expanded manifest (13 file cases) + fair multi builtin → **golden 30/30**
- `logic-sat drat-fuzz` external DRAT fuzz loop
- `logic-sat hard` portfolio directory bench (`portfolio_bench.zig`)
- Fair multi depth: 2J+2F one stuck, justice+fairness toggle, round-robin attach

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
