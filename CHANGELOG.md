# Changelog

All notable changes to **logic-zig** are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project aims to follow [Semantic Versioning](https://semver.org/).

## [0.19.0] — 2026-08-04

### Push the universal edge

- **`deductive/sequent`**: LK sequent calculus (prop) — Γ ⊢ Δ, structural + logical rules, checked proof nodes
- **`paraconsistent/lp`**: Belnap-Dunn four-valued / Logic of Paradox — T/F/B/N; explosion fails by design
- **`historical/syllogistic`**: Aristotelian categorical syllogistic — 24 valid moods × 4 figures (Barbara…Fresison)
- **`nonmonotonic/default`**: Reiter default logic — propositional extensions, ≤12 defaults exhaustive
- Registry: sequent-lk, paraconsistent, syllogistic, default-logic → **fragment**
- STATUS v0.19.0

### Residual

- No automated sequent proof search / focusing yet
- Defaults are Reiter-style only (no priorities / ASP)
- Syllogistic is validity table, not a term-logic prover

## [0.18.0] — 2026-08-04

### Modes of reasoning: induction · abduction · fuzzy · natural deduction

- **`abductive/abduce`**: propositional abduction via CDCL; ≤16 abducibles
- **`inductive/induction`**: mathematical induction schema + Peano/List
- **`fuzzy/fuzzy`**: Gödel / product / Łukasiewicz + Kleene 3-valued
- **`deductive/natded`**: Fitch-style natural deduction fragment
- Registry raised to fragment; STATUS v0.18.0

## [0.17.0] — 2026-07-17

### Universal logic platform

- taxonomy registry, informal argument, MLTT micro, modal K, giants discover
- CLI: `taxonomy`, `giants`, `edge-suite`

## Earlier

See git history for 0.1–0.16 industrial SAT/MC/SMT program.
