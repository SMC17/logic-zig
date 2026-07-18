# Changelog

All notable changes to **logic-zig** are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project aims to follow [Semantic Versioning](https://semver.org/).

## [0.21.0] — 2026-07-17

### Classical-adjacent wave: intuitionistic · many-valued · epistemic · syllogistic · EL

- **`logic/intuitionistic.zig`**: G4ip (Dyckhoff contraction-free) decision procedure for
  intuitionistic propositional validity — immutable contexts, no loop checking; canon
  (Peirce/LEM unprovable, double negations provable) + 80-formula Glivenko cross-check
  against a classical truth-table oracle. A context-corruption bug in the first
  mutate-and-restore draft was caught by the pre-registered Glivenko falsifier.
- **`logic/manyvalued.zig`**: finite logical matrices — classical, K3, LP, FDE, Ł3 with
  designated-value consequence; canon: LP paraconsistency (explosion & MP fail, LEM holds),
  K3 gaps (no p→p), Ł3 contraction failure, FDE gap+glut; classical matrix verified
  against truth tables on random formulas
- **`modal/epistemic.zig`**: multi-agent S5 model checking with K/E/common-knowledge
  (reachability fixpoint) and public announcements; full muddy-children canon (n=3),
  S5 introspection properties, everybody-knows vs common-knowledge separation
- **`logic/syllogistic.zig`**: complete categorical-syllogism decision via Venn-region
  enumeration (2^8 patterns = exact semantics): exactly 15 Boolean-valid and 24
  import-valid of 256 forms; Barbara/Celarent/Darii/Ferio/Darapti/Barbari/Baroco/Bocardo
  named checks; AAA-2 fallacy rejected
- **`logic/el.zig`**: description logic EL subsumption — normalization to the four EL
  normal forms + completion-rule saturation; role-chain, conjunction and pericarditis
  canon fixtures with exact closure (no spurious subsumptions)
- **api/v1 → 1.4.0**: five new capability bits + re-exports
- Taxonomy: intuitionistic-prop, fuzzy/many-valued, paraconsistent, epistemic,
  syllogistic, description-al all advance `documented` → `fragment`
- Pre-registered: exp-1784333657-083950258 (G4ip), exp-1784333658-394375372 (matrices),
  exp-1784333658-988061669 (epistemic), exp-1784333662-689272384 (syllogistic),
  exp-1784333663-779933697 (EL)

## [0.20.0] — 2026-07-17

### Nonmonotonic completion wave: argumentation · answer sets · belief revision · circumscription · analogy

- **`reason/argumentation.zig`**: Dung AFs — grounded via characteristic-function fixpoint;
  admissible/complete/stable/preferred enumeration; credulous & skeptical acceptance;
  canon: reinstatement, mutual attack, odd/even cycles, floating acceptance,
  grounded ⊆ every preferred
- **`reason/asp.zig`**: stable models of normal programs — Gelfond–Lifschitz reduct
  least-model check as the certificate; canon: even/odd negative loops, constraints,
  stratified programs, supported-but-unfounded models rejected
- **`reason/agm.zig`**: AGM base contraction via remainder sets (maxichoice, full-meet,
  cardinality partial-meet) + Levi-identity revision; postulate tests: success, inclusion,
  vacuity, tautology-failure, revision consistency
- **`reason/circumscription.zig`**: propositional circumscription — P-minimal-model
  entailment with fixed/varying atoms via signature enumeration over the SAT oracle;
  bird/ab canon, exception defeat; 30 random instances cross-checked against an
  independent full-assignment oracle
- **`reason/analogy.zig`**: Boolean analogical proportions (Miclet–Prade) — axioms
  verified over 200 random vectors + exhaustive 16-pattern check; unique-solution
  solving; analogical classifier exact & unanimous on affine concepts, **abstains**
  when no label-solvable triple exists (minimal-XOR honesty test)
- **api/v1 → 1.3.0**: Capability widened to u64 (low word unchanged, `toU32` kept);
  5 new bits; re-exports for all five engines
- Taxonomy: +5 fragment rows (dung-af, asp-stable, agm-revision, circumscription,
  analogical); coverage doc: Analogical and Dialogical/argumentation modes now M
- Pre-registered: exp-1784310435-261237507 (AF), exp-1784310435-294505035 (ASP),
  exp-1784310435-326080521 (AGM), exp-1784310439-633429721 (circumscription),
  exp-1784310439-666082653 (analogy)

## [0.19.0] — 2026-07-17

### Reasoning-mode wave: MaxSAT · cost-ranked & first-order abduction · Bayesian induction · nonmonotonic family

- **`sat/maxsat.zig`**: weighted partial MaxSAT — exact optimum via descending upper-bound
  search with a sequential weighted counter PB encoding; verified against brute force on
  60 random instances
- **`reason/abduction.zig` + `abduceMinCost`**: cost-optimal explanations via the implicit
  hitting-set duality (min-cost hitting sets of accumulated MCSes via MaxSAT, candidates
  checked deductively, inconsistent candidates blocked); cardinality-minimal by default,
  weighted objectives supported; brute-force cross-checked incl. 25 random instances
- **`reason/alp.zig`**: abductive logic programming — **first-order abduction** over the
  Horn substrate: SLD with hypothesis collection (KKT-style, definite fragment), trail-based
  Robinson unification with occurs check, integrity denials with variables, set-semantic Δ,
  independent deductive re-check (`derives`); hypotheses genuinely instantiated by
  unification (flies(tweety) → normal(tweety))
- **`reason/bayes.zig`**: Bayesian/statistical induction — Laplace rule of succession
  (Beta priors) and exact posterior over the conjunction hypothesis class with Occam prior
  and ε-noise likelihood; MAP + predictive by full model averaging
- **`reason/default_logic.zig`**: Reiter default logic — extension enumeration with
  groundedness, justification consistency against the final extension, and stability;
  credulous/skeptical consequence; canon: Tweety, Nixon diamond (2 extensions),
  ( :p / ¬p ) (0 extensions), self-support rejected, inconsistent-W degeneracy
- **`reason/klm.zig`**: KLM rational closure — Lehmann–Magidor exceptionality ranking and
  entailment, all SAT-backed; canon: specificity overrides, irrelevance preserved
  (red bird flies), nonmonotonicity, vacuous impossible antecedents
- **api/v1 → 1.2.0**: six new capability bits + re-exports for all engines
- Taxonomy: `default-logic`, `probabilistic` → `fragment`; new rows `klm-rational`,
  `alp`, `maxsat`
- CLI: `reason-demo` exercising all five new engines
- Pre-registered and confirmed: exp-1784300107-552194486 (MaxSAT),
  exp-1784300107-605449209 (min-cost abduction), exp-1784300112-349635420 (ALP),
  exp-1784300112-405562520 (Bayes), exp-1784300117-164722046 (defaults),
  exp-1784300117-228825284 (rational closure)

## [0.18.0] — 2026-07-17

### Peircean triad: abduction and induction as first-class engines

- **`reason/abduction.zig`**: propositional abduction — B ∧ H ⊨ O with H ⊆ abducibles,
  **subset-minimal** (deletion-minimal MUS via `solveAssumptions`) and **background-consistent**;
  MARCO-style enumeration (UNSAT seeds shrink to MUS, SAT seeds grow to MSS, map solver prunes);
  `verifyExplanation` re-certifies any answer with fresh solvers
- **`reason/induction.zig`**: inductive synthesis — exact SAT encoding of k-term DNF
  consistency over labeled boolean examples; iterative deepening gives **minimal k**
  (Occam), hypotheses deductively re-verified on every example; distinct from
  `circuit/kinduction.zig` (which is deductive invariant checking)
- Deduction is the shared oracle for both — the triad is now engines, not taxonomy labels
- **api/v1 → 1.1.0**: `abduce` / `induceDnf` re-exports; capability bits
  `reason_abduce` / `reason_induce`
- Taxonomy: `inductive` and `abductive` rows advance `documented` → `fragment`
- CLI: `abduce-demo` (diagnosis: minimal causes, verified), `induce-demo` (learns xor at k=2)
- Pre-registered: `exp-1784298692-629536463` (abduction minimality/consistency),
  `exp-1784298694-561301438` (induction consistency/minimal-k)

## [0.17.0] — 2026-07-17

### Universal logic platform (destination, not finished completeness)

- **`docs/UNIVERSAL.md`**: north star — taxonomy, giants, informal, TT, forever deepen
- **`taxonomy/registry`**: named systems × maturity across classical / modal / constructive / informal / external
- **`informal/argument`**: argument graphs, schemes, structural checks
- **`type_theory/tt`**: MLTT micro (contexts, Π, Id, check)
- **`modal/kripke`**: finite Kripke eval (□/◇)
- **`bridge/giants`**: discover Kissat/Z3/ABC/Vampire/Lean/Coq/CaDiCaL/drat-trim
- CLI: `taxonomy`, `giants`, `edge-suite`
- Honesty: no claim of finished universal engines or solver parity

## [0.16.0] — 2026-07-16

### Industrial wave: vivify · sat_hard · UF · ABC path

- **Vivification** in preprocess (literal/clause strengthen via UP under ~others)
- **sat-scoreboard --industrial**: portfolio + vivify + higher timeout; `sat_hard` CI sample
- **SMT UF spine** (`smt/uf.zig`): congruence closure, diseq, unary preds; capability `smt_uf=true`
- **MC edge bar**: empty-bad, multi-bad OR, constraint-only, init×constraint vacuity,
  dual-rail / one-hot / counter bounds designs + golden AIGER fixtures; `mcAiger` multi-prop
- **ABC path**: `abc-delta` compares internal MC vs ABC PDR when `abc` present;
  `deltaLabel` full unit matrix without ABC
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
