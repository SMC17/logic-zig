# Industrial program — how logic-zig becomes the best *Zig* logic stack

**Thesis:** Own the full formal stack **in Zig**, with industrial *quality goals*
and honest *maturity levels*. Not “ship Z3 next week” — a multi-horizon program
with falsifiers at every gate.

**Shipped baseline:** v0.14.0 (competition tracks, trust, agent, PDR/BMC/kind).

## Target map (what “achieved” means)

| Pillar | Industrial bar (falsifier) | Maturity now |
|--------|---------------------------|--------------|
| **Stable API** | Semver `logic.api.v1`, capability matrix, spin-offs only use v1 for public ops | **Phase 0 — landing** |
| **Industrial SAT** | 0 mismatches vs CaDiCaL on fixed suite; rising solved@budget on `sat_hard` / `sat_comp` | Mid kernel (CDCL+portfolio) |
| **Industrial MC** | HWMCC-style suite slice; certs on proven; ABC Δ when available | BMC/kind/PDR real; not ABC-class |
| **ABC-class sequential** | Interop + own engines on designs; optional `abc` baseline | Interop probe only |
| **Industrial SMT** | BV solid + theory combo (UF/arrays) via DPLL(T)-lite | BV bit-blast micro |
| **Full FOL prover** | Resolution/superposition on TPTP-style CNF; soundness tests | Unify + finite models |
| **CTL / BV** | Bounded CTL complete for supported ops; BV ops industrial | Bounded CTL + BV-lite |

## Dependency order (do not scramble)

```
Stable API (v1)
    │
    ├─► Industrial SAT  ─────────────────────────────┐
    │         │                                        │
    │         ├─► Industrial SMT (DPLL(T) on SAT)     │
    │         └─► FOL CNF resolution (SAT-like loop)  │
    │                                                  │
    └─► Sequential MC (uses SAT) ─► ABC interop/Δ ────┘
              │
              └─► CTL (unroll / fair) · designs · certs
```

**Rule:** No new pillar without (1) API surface, (2) unit tests, (3) trust or
golden hook, (4) STATUS residual if not industrial.

## Phases

### Phase 0 — Stable API · *now*
- `src/api/v1.zig`: version, `Capability`, high-level `sat` / `mc` / `smt` / `fol` / `ctl`
- Deprecation policy: internals may change; `api.v1` is the contract
- **Falsifier:** spin-offs or tests fail; missing capability bits

### Phase 1 — Industrial SAT · *active*
- Preprocess: subsumption, BCP, pure, self-subsume, **vivification**
- Inprocessing: satisfied learned deletion (`inprocess_interval`)
- Scoreboard: `sat-scoreboard` / `--industrial` on `sat_comp` + **`sat_hard`**
- **Falsifier:** mismatches > 0 when both decide; crash
- **PAR-2:** measured; WIN not required for phase pass (correctness is)

### Phase 2 — Industrial MC + ABC · *path live*
- `abc-delta <aig>` internal vs ABC; soft-skip if ABC missing
- **Falsifier:** `delta=MISMATCH` when both decide

### Phase 2 — Industrial MC + ABC-class *path*
- PDR/IC3 depth (generalize, clause sharing, better CTG)
- ABC interop: run safety command when present; Δ on fixtures
- Design library growth; HWMCC track cert density
- **Falsifier:** trust sequential fail; golden drop

### Phase 3 — Industrial SMT · *UF spine*
- `SmtSolver` + BV + **ground EUF** (`uf.zig` congruence / diseq / preds)
- Arrays / UFBV still unsupported
- **Falsifier:** wrong EUF unsat/sat on unit tests

### Phase 4 — Full FOL prover
- Clausal FOL + resolution + subsumption + given-clause
- Finite model finder retained for countermodels
- Later: superposition / paramodulation (Phase 4b)
- **Falsifier:** unsound proof; fails basic CNF FOL unsat

### Phase 5 — CTL / BV polish + ecosystem
- Fair CTL depth; BV word-level rewrites
- C ABI stability for IPASIR; docs as product
- External consumers

## Honesty clause

“Industrial” here means **measurable approach to industrial quality**, not a
claim of parity with Kissat / ABC / Z3 / Vampire on day of tag. STATUS.md
residuals stay sacred. Type-I overclaim is a failure mode.

## Climb commands

```sh
zig build test && zig build
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig doctor
# after API lands:
# zig test / capability print via doctor or api-demo
```
