# Bounded Linear Temporal Logic (LTL)

## Formal identity

LTL over **finite traces** of length ≤ `bound`: frames `0..bound`, each frame a
Boolean state vector. Supported fragment:

- `ap(p)` — atomic proposition (net `p` true at the current frame)
- `¬φ`, `φ ∧ ψ`, `φ ∨ ψ`
- `X φ` — next: φ holds at frame `i+1` (false if `i` is the last frame)
- `F φ` — eventually: φ holds at some frame `j ≥ i`
- `G φ` — globally: φ holds at every frame `j ≥ i`
- `φ U ψ` — until: ψ holds at some `j ≥ i` and φ holds at all `k ∈ [i, j]`
- `φ R ψ` — release: ψ holds at every `j ≥ i`, or φ holds at some `k ∈ [i, j]`

Bounded semantics is **honest**: this decides LTL on finite traces, not the
ω-regular / full-LTL model-checking problem. Results are therefore labelled
`holds_within_bound` / `fails_within_bound`, never an unbounded proof.

## Two independent semantics (cross-checked)

1. **`evalDirect`** — recursive structural evaluation over an explicit `Trace`
   (array of frame state vectors). No SAT involved.
2. **`evalSat`** — textbook bounded LTL→SAT encoding: one Boolean variable per
   (subformula, frame), Tseitin clauses for every operator and its recursive
   `next` link, solved by the CDCL core. The formula holds at frame 0 iff the
   root variable is forced satisfiable.

The module's test suite asserts the two evaluators agree on thousands of random
(trace, formula) pairs; any divergence is a hard test failure.

## Exhaustive oracle

Random traces (1–4 frames, 1–2 nets) × a basket of formulas are checked for
agreement, and textbook validities are asserted:

- `F p ↔ ¬G ¬p` (duality) on every finite trace
- `p U q → F q` on every finite trace
- `G p → p` at frame 0 on every finite trace
- fail-closed `verifyClaim`: a recorded verdict must match **both** evaluators;
  any divergence or expected/actual mismatch traps rather than passing silently.

## Honest limitations

- Finite-trace only. `X φ` at the final frame is false (off-end bounded
  semantics); this is not the infinite-path `X`.
- No parser — formulas are built via the `Builder` arena.
- No deductive calculus / proof objects; this is a model-checking decision
  procedure, not a theorem prover.
- State is a flat Boolean net vector; no explicit Kripke labeling beyond the
  net's own nets.

## Source

`src/ctl/ltl.zig` — `Trace`, `Builder`, `Formula`, `evalDirect`, `evalSat`,
`check`, `verifyClaim`, `crossCheck`.
