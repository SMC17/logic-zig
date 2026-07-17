# Logic taxonomy coverage — honest map for logic-zig

**Destination:** a **universal** Zig logic library (see `UNIVERSAL.md`) — every
named family appears in the registry; engines deepen over time; giants fill
industrial gaps until we match or surpass them with evidence.

**Question:** Do we implement every edge of the master taxonomy *today*?

**Answer: No — not as finished engines.** We **register** the map, ship **depth**
where we are strong, and **never hide** empty cells. Completeness is a program.

Proof level: **audited map** against the codebase at v0.16+ (update with each major).

---

## 1. Coverage legend

| Code | Meaning |
|------|---------|
| **S** | Shipped engine/API with unit/integration tests |
| **M** | Micro / fragment / spine only |
| **P** | Planned industrial program (`docs/INDUSTRIAL.md`) |
| **I** | Interop / external tool only |
| **—** | Out of scope for this library |

---

## 2. Broadest divisions

| Branch | Status | Notes |
|--------|--------|-------|
| Formal / symbolic / computational logic | **S** | Core product identity |
| Mathematical logic (fragments) | **M** | FOL finite models, resolution; not set theory |
| Philosophical logic | **—** | Not a philosophy engine |
| Informal logic / rhetoric | **—** | Natural-language argumentation |
| Metalogic (as meta-theorems) | **M** | Soundness tests, DRAT/RUP, trust-report; not a meta-prover |
| Algebraic / categorical logic | **—** | |
| Applied domain logics (law, ethics, …) | **—** | Downstream of core |

---

## 3. Mode of reasoning

| Mode | Status |
|------|--------|
| Deductive (classical computational) | **S** |
| Inductive / Bayesian / statistical | **M** — `reason/induction.zig` (SAT-exact minimal-k DNF synthesis) + `reason/bayes.zig` (exact posterior over conjunction class, Occam prior, model-averaged prediction, Laplace succession) |
| Abductive | **M** — `reason/abduction.zig` (subset-minimal + min-cost via MaxSAT hitting sets) + `reason/alp.zig` (first-order SLD abduction with denials) |
| Analogical | **—** |
| Defeasible / nonmonotonic | **M** — `reason/default_logic.zig` (Reiter extensions) + `reason/klm.zig` (rational closure) |
| Probabilistic logics | **M** — `reason/bayes.zig` (finite exact Bayesian; no graphical models / MCMC) |
| Causal (Pearl, etc.) | **—** |
| Practical / deontic / decision | **—** |
| Dialogical / argumentation frameworks | **—** |

---

## 4. Classical symbolic core (our home turf)

| System | Status | Evidence |
|--------|--------|----------|
| Classical propositional | **S** | ExprPool, Tseitin, CDCL, IPASIR |
| Clausal / CNF / Horn-ish | **S** | `sat/*`, preprocess, portfolio |
| Classical FOL (fragment) | **M** | terms, unify, finite models, resolution skeleton |
| FOL with equality (EUF ground) | **M** | `smt/uf.zig` congruence |
| Higher-order / HOL | **—** | |
| Infinitary | **—** | |
| Second-order | **—** | |
| Free logic / empty domains | **—** | |
| Sorted / many-sorted | **—** | |
| Team / dependence logic | **—** | |

---

## 5. Constructive / intuitionistic / type theory

| Family | Status |
|--------|--------|
| Intuitionistic / intermediate | **—** |
| Linear / relevant / substructural | **—** |
| Martin-Löf / HoTT / CoC | **—** |
| Realizability | **—** |

*(Proof assistants live elsewhere: Lean, Coq, Agda.)*

---

## 6. Modal / temporal / multi-agent

| Family | Status |
|--------|--------|
| LTL / CTL (bounded) | **M** | `ctl/*` bounded SAT unrolling |
| Infinite-trace fairness | **S/M** | k-liveness, justice |
| Full LTL/CTL* symbolic | **—** | |
| Epistemic / deontic / dynamic logic | **—** | |
| μ-calculus complete | **—** | |

---

## 7. Computational logic (product center)

| Area | Status | Notes |
|------|--------|-------|
| SAT / CDCL | **S** | Industrial program Phase 1 |
| SMT (BV) | **M→P** | bit-blast |
| SMT (UF) | **M** | ground EUF |
| SMT (arrays) | **M/P** | spine if present |
| Model checking (safety) | **S** | BMC, k-ind, PDR |
| Model checking (liveness) | **S/M** | justice, k-live |
| ATP (resolution) | **M** | FOL CNF resolution |
| Superposition / paramodulation | **P** | |
| Logic programming (Prolog/ASP) | **—** | |
| Description logics / OWL | **—** | |
| Program verification / CHC | **P** | via BMC/PDR path |
| Proof assistants | **—** | |
| IPASIR embedding | **S** | |
| Certificates (RUP/DRAT/inv) | **S/M** | |
| Competition tracks | **S** | sat-track, hwmcc-track, scoreboard |

---

## 8. Many-valued / fuzzy / quantum / non-classical

| Family | Status |
|--------|--------|
| Finite-valued / Łukasiewicz / Gödel | **—** |
| Fuzzy | **—** |
| Paraconsistent | **—** |
| Quantum logic | **—** |
| Probabilistic logic | **—** |

---

## 9. Historical / term / natural language logics

| Family | Status |
|--------|--------|
| Aristotelian / syllogistic | **—** |
| Medieval consequence | **—** |
| Natural logic / NLI | **—** |
| Indian / Arabic logical traditions | **—** |

---

## 10. What “raise the bar as high as possible” means *here*

We **do not** implement the taxonomy. We **maximize depth and edge coverage** inside the
**computational classical + sequential + SMT/FOL fragment** product:

1. **Edges** — empty/unit/xor/pure/vivify/preprocess; AIGER const/constraint/init; UF chains; resolution.
2. **Depth** — industrial SAT scoreboard vs CaDiCaL; PDR/kind/BMC; certs; agent multishot.
3. **Honesty** — capability bits, STATUS residuals, this map.
4. **Interop** — CaDiCaL, drat-trim, ABC when present.

Commands:

```sh
./zig-out/bin/logic-zig edge-suite
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat_hard --limit 8 --industrial
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig api-info
```

---

## 11. Non-goals (explicit)

- Universal logic library for all named systems in the taxonomy.
- Informal argument analysis.
- Full type theory / proof assistant.
- Beating Kissat/ABC/Z3/Vampire as identity.
- Philosophical completeness.

---

## 12. Update rule

When a new engine lands, update this table in the same PR as STATUS.md.
Never mark **S** without a test gate. Never erase a residual without evidence.
