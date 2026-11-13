# logic-zig status

**Version:** 0.24.0  
**North star:** executable museum and agent-trust kernel in Zig. SAT/MC is
substrate; completeness is local to a named system
([`docs/UNIVERSAL.md`](docs/UNIVERSAL.md)).

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig giants
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-hwmcc golden
```

## Zig-side residual closure (v0.24)

| Residual | Module | Status |
|----------|--------|--------|
| Pairwise blocking + ≥n | `description/pairwise` | **fragment** |
| HO pattern unification | `type_theory/huet` | **fragment** |
| WPLL objective | `probabilistic/wpll` | **fragment** |
| Modal forcing traces | `modal/trace` | **fragment** |
| KLM + ranked countermodels | `nonmonotonic/klm` | **fragment** |
| MV fixture schema (Lean differential) | `manyvalued/fixtures` | **fragment** |
| Lean oracle contract | `docs/LEAN_ORACLE.md` | documented |

## What remains outside pure Zig `main`

These need **external processes**, not more library spines:

| Item | Why |
|------|-----|
| Issue **#3** Lean↔Zig fixtures | Requires pinned Lean 4 + `lake build` + CI nanoda; Zig schema is ready |
| Issue **#5** museum Lean frame proofs | Requires Lean formalization of frame conditions |
| Issue **#6** upstream contributions | Human upstream PR loop (Aristotle/Lean projects) |
| PR **#2** museum draft | Rebase onto current `main` + evidence gates |
| Industrial parity Kissat/Z3/Vampire | Scoreboard only; never claimed |

## Host portability and trust gates

Host discovery, monotonic timing, proof/export writes, and file-size checks use
Zig 0.16 platform-aware APIs. Native core CI is configured for Linux and macOS; Windows
runtime behavior remains unverified. The core smoke suite is distinct from the
independent-checker trust gate.

`TRUST_OK` requires positive DRAT verification, completed CaDiCaL differential
checks, ABC availability, and positive results on every internal evidence axis.
No missing checker or zero-run axis counts as successful evidence. See
[`docs/GETTING_STARTED.md`](docs/GETTING_STARTED.md) for pinned checker setup.

### Native verification, 12 November 2026

After merging the museum and Lean-oracle branch (#2): on macOS ARM64 with
Zig 0.16.0, `zig build test --summary all` passes 541/541 and
`zig fmt --check src build.zig` is clean.

### Native verification, 11 November 2026

On macOS ARM64 with Zig 0.16.0: `zig build test --summary all` passes
391/391 tests; build, doctor, proof export, and AIGER round-trip pass.
Pinned independent tools produce `TRUST_OK`: 5 DRAT verifications,
25 CaDiCaL comparisons with no mismatches, ABC available, and all internal
evidence axes passing. The Linux x86-64 cross-build also passes; this is
compile evidence, not a Linux runtime result. No performance parity is claimed.

## Engine and fragment coverage

**Engines:** CDCL, BMC/k-ind/PDR/klive, IPASIR, DRAT, taxonomy.  
**Fragments:** ND, sequent, focusing, search, abduction ladder, IPC, linear, relevance, K–S5 + certs + traces, epistemic/deontic, fuzzy/LP + fixtures, MLN + lifted + WPLL, ALC/SHIQ + subset/pairwise blocking, HOL + resolution + pattern unify, categorical, syllogistic, defaults, KLM countermodels.

Cite: [`CITATION.cff`](CITATION.cff). Graph: [`GRAPH.md`](GRAPH.md). Lean: [`docs/LEAN_ORACLE.md`](docs/LEAN_ORACLE.md).

https://github.com/SMC17/logic-zig
