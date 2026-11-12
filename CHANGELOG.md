# Changelog

All notable changes to **logic-zig** are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project aims to follow [Semantic Versioning](https://semver.org/).

## [Unreleased]

### Trust evidence

- Require an exact DRAT checker success status and exit 0. Reject negative,
  conflicting, diagnostic-only and failed-checker output. Patch the pinned
  checker build's incorrect exit status on an input containing an empty clause.
- Refuse `sat --check-drat` when independent checking is unavailable; reject
  formula-mode requests that previously silently ignored that option.
- Add `trust-report --json` with versioned counters, scope and derived status.
- Add a deployment policy example with independent proof replay, rejection
  after changing the input, and a local receipt binding artifacts to hashes.

### Packaging

- Add seven-CLI clean-source packs, task-oriented entry points, checksums and a gated native preview workflow. External proof checkers remain a separate installation.


### Fixed

- Host discovery, monotonic timing, proof/export writes, and file-size checks
  use Zig's platform-aware APIs instead of direct Linux system calls.
- External-tool discovery reads the startup environment on native platforms
  without depending on `/proc`. Temporary solver inputs are removed after use.
- Proof and AIGER writes report failures instead of ignoring partial writes.

- `trust-report` now requires positive evidence on every required axis and
  refuses missing independent checkers or inconclusive differential checks.
- `logic-sat check-drat` no longer returns UNSAT success without a verified
  external proof. CI builds pinned checkers and explicitly checks SAT exit codes.

### Docs

- Visitor README: executable museum / agent-trust kernel (not a SAT-solver pitch).
  Version badge aligned with STATUS 0.24.0. Lean kernel and fail-closed museum CLI
  remain named residuals.

## [0.21.0] — 2026-08-04

### Depth attack + project surface

- **`deductive/focusing`**: Andreoli focusing (inversion/focus phases)
- **`description/shiq`**: SHIQ role hierarchy, inverse, transitive, ≥n/≤n
- **`probabilistic/markov`**: Markov logic weighted worlds + marginals
- **`abductive/mus`**: complete deletion-minimal MUS + Berge hitting-set abduction
- **`substructural/relevance`**: relevance logic R variable-sharing + fusion spine
- **Docs overhaul**: README (universal platform), GRAPH.md, SECURITY.md, CODE_OF_CONDUCT.md, CONTRIBUTING, STATUS
- Issue #1 (dependency graph) resolved via GRAPH.md

## [0.20.0] — 2026-08-04

### Remaining taxonomy edges

- Intuitionistic IPC (finite Kripke; LEM countermodel)
- Linear logic ILL + resource bags
- Epistemic Kᵢ + deontic O/P
- Probabilistic independence + Fréchet
- ALC description logic tableau spine
- Automated sequent search
- Industrial (greedy) abduction

## [0.19.0] — 2026-08-04

### Universal edge

- LK sequent calculus, paraconsistent LP, Aristotelian syllogistic, Reiter defaults

## [0.18.0] — 2026-08-04

### Modes of reasoning

- Abduction, mathematical induction, fuzzy t-norms, Fitch natural deduction

## [0.17.0] — 2026-07-17

### Universal logic platform foundation

- Taxonomy registry, informal argument, MLTT micro, modal K, giants discover

## Earlier

See git history for 0.1–0.16 industrial SAT/MC/SMT program.
