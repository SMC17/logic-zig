# Universal logic library — destination for logic-zig

## Ambition (explicit)

**logic-zig is the Zig home for computational logic that refuses artificial
ceilings.** We aim at:

1. **A registry of named systems** across the master taxonomy (classical,
   constructive, modal, substructural, many-valued, informal, type-theoretic, …).
2. **Native engines** where Zig can own the substrate (SAT, MC, SMT fragments,
   FOL cores, certificates, agent multishot).
3. **Standing on giants** where decades of C/C++ already won (Kissat, CaDiCaL,
   ABC, Z3, Vampire, Lean/Coq *as peers and oracles*) — interop, differential
   testing, optional subprocess/API bridges.
4. **Informal argument analysis** as a first-class module (schemes, structure,
   not only CNF).
5. **Type theory / proof-assistant spines** (contexts, judgments, micro checkers)
   that can grow toward full assistants.
6. **Philosophical completeness as a *program***: capability bits and maturity
   for alethic, epistemic, deontic, temporal, … — never silent absence.

We will always be able to go further. That is a feature. **Ship maturity, not
fiction.**

## Non-fiction rule

| Claim | Allowed only when |
|-------|-------------------|
| “Supports system X” | Registry entry + API + test, maturity ≥ `skeleton` |
| “Industrial parity with Kissat/Z3/…” | Scoreboard evidence on fixed suites |
| “Full type theory / proof assistant” | Kernel + elaborator + library, not a stub |
| “Philosophical completeness” | Documented coverage matrix; open cells listed |

Absence is recorded as `maturity = absent` or `external_only`, never hidden.

## Architecture

```
                    ┌──────────────────────────────┐
                    │     taxonomy.registry        │
                    │  named systems × maturity    │
                    └──────────────┬───────────────┘
           ┌───────────────────────┼───────────────────────┐
           ▼                       ▼                       ▼
    native engines           informal / TT            giants interop
    SAT MC SMT FOL           argument · types         Z3 Kissat ABC
    CTL modal µ             schemes · contexts        Vampire CaDiCaL
           └───────────────────────┬───────────────────────┘
                                   ▼
                         api/v1 + certificates + agent
```

## Maturity ladder (per named system)

| Level | Meaning |
|-------|---------|
| `absent` | Not started |
| `documented` | Named in registry only |
| `skeleton` | Types/API/tests that link; may unsupported |
| `fragment` | Real algorithms on a decidable slice |
| `engine` | Production path inside logic-zig |
| `industrial` | Scoreboard vs external peer |
| `external` | Delegated entirely to a giant (with adapter) |

## How we leave no stone unturned

1. **Registry-first:** every taxonomy branch has at least a row.
2. **Edge suite:** adversarial tiny cases per live engine.
3. **Giants:** auto-discover installed solvers; never reimplement before measuring.
4. **Depth loops:** industrial program (`INDUSTRIAL.md`) for SAT/MC/SMT/FOL.
5. **Horizon backlog:** each major family has a Phase N entry, not a graveyard.

## Commands

```sh
./zig-out/bin/logic-zig taxonomy          # list systems × maturity
./zig-out/bin/logic-zig giants            # discover external peers
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
```

## Relation to other docs

- `TAXONOMY_COVERAGE.md` — detailed map vs the master taxonomy
- `INDUSTRIAL.md` — computational depth (SAT/MC/SMT/FOL)
- `TRUST.md` — certificates and honesty gates
