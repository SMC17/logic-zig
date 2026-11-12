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

Proof acceptance requires an exact positive checker status and normal exit 0;
the pinned DRAT-trim build includes an explicit empty-clause exit-status patch.
`trust-report --json` exposes the finite-suite evidence to consumers. The
[deployment policy example](examples/policy/README.md) exports a proof and
checks its acceptance and rejection against two explicit inputs. Connecting
that example to real action authorization remains application work.

### Native verification, 11 November 2026

On macOS ARM64 with Zig 0.16.0: `zig build test --summary all` passes
391/391 tests; build, doctor, proof export, and AIGER round-trip pass.
Pinned independent tools produce `TRUST_OK`: 5 DRAT verifications,
25 CaDiCaL comparisons with no mismatches, ABC available, and all internal
evidence axes passing. The Linux x86-64 cross-build also passes; this is
compile evidence, not a Linux runtime result. No performance parity is claimed.

### Trust evidence verification, 12 November 2026

On native macOS ARM64 with Zig 0.16.0, Debug and ReleaseSafe each pass
393/393 tests. The CLI refusal suite rejects missing, negative, conflicting,
nonzero-exit and inconclusive checker results, and rejects a policy-demo receipt
from a checker that blindly repeats success. The JSON trust run with patched
pinned DRAT-trim, pinned CaDiCaL and ABC reports `TRUST_OK`: 5 DRAT verifications,
25 differential runs, zero mismatches, and positive internal axes. The policy
demo passes proof export, independent acceptance, SAT after weakening the policy,
and rejection of the old proof against that changed input. These are native
local measurements; no new hosted CI or Linux runtime result is claimed.

## Engine and fragment coverage

**Engines:** CDCL, BMC/k-ind/PDR/klive, IPASIR, DRAT, taxonomy.  
**Fragments:** ND, sequent, focusing, search, abduction ladder, IPC, linear, relevance, K–S5 + certs + traces, epistemic/deontic, fuzzy/LP + fixtures, MLN + lifted + WPLL, ALC/SHIQ + subset/pairwise blocking, HOL + resolution + pattern unify, categorical, syllogistic, defaults, KLM countermodels.

Cite: [`CITATION.cff`](CITATION.cff). Graph: [`GRAPH.md`](GRAPH.md). Lean: [`docs/LEAN_ORACLE.md`](docs/LEAN_ORACLE.md).

https://github.com/SMC17/logic-zig
