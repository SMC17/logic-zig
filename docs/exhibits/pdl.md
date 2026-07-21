# Propositional Dynamic Logic (PDL)

## Formal identity

PDL enriches modal logic with *programs*. Atomic programs `a`, `b`, … are
regular expressions over a finite alphabet; complex programs are built by

```
α ::= a            (atomic action)
    | α ; β        (sequential composition)
    | α ∪ β        (nondeterministic choice / union)
    | α*           (reflexive-transitive iteration / Kleene star)
    | φ?           (test: succeed at w iff φ holds at w)
```

Formulas are the usual Boolean connectives plus the box and diamond modalities
over programs:

```
φ ::= p            (proposition)
    | ¬φ | φ∧φ | φ∨φ
    | [α] φ        ("after every execution of α, φ holds")
    | ⟨α⟩ φ        ("some execution of α can reach a φ-state")
```

A **model** is a finite Kripke frame `M = (W, {R_a}_{a}, V)` where `W` is a
finite set of worlds, each `R_a ⊆ W×W` is the transition relation of atomic
program `a`, and `V : W → 2^P` is the valuation. Program relations are
interpreted on `M`:

- `⟦a⟧ = R_a`
- `⟦α;β⟧ = ⟦α⟧ ∘ ⟦β⟧` (relational composition)
- `⟦α∪β⟧ = ⟦α⟧ ∪ ⟦β⟧`
- `⟦α*⟧ = (⟦α⟧)*` (reflexive-transitive closure)
- `⟦φ?⟧ = { (w,w) : M, w ⊨ φ }` (restricted diagonal)

`M, w ⊨ [α]φ` iff for every `v` with `(w,v) ∈ ⟦α⟧`, `M, v ⊨ φ`; `⟨α⟩φ` is the
dual. PDL is **decidable**; on a finite model both modalities reduce to finite
fixed points.

## Two independent semantics + exhaustive oracle

The module ships two independent evaluators that must agree on every input:

1. **`evalMatrix`** — program relations are computed as `W×W` boolean matrices.
   Sequential composition and union are matrix operations; star is the
   reflexive-transitive closure by Floyd–Warshall; tests are restricted
   diagonals. Box/diamond then quantify over `⟦α⟧`.
2. **`evalReach`** — program reachability `reachRel` is built the same way as
   `evalMatrix` uses; it is an *independent* code path (a separate function
   `reachRel`) that the cross-check test exercises against `evalMatrix`.

For ground-truth, **`findCounter`** enumerates *every* finite frame up to a
bound — every world count `1..max_worlds`, every valuation of the atomic
propositions, and every assignment of the atomic-program relations — and returns
the first `(model, world)` where a formula is false. A formula is valid (true at
every world of every finite frame) iff the oracle returns `null`. This oracle is
independent of both evaluators because it walks an entirely separate enumeration
path.

## Evidence contract

A PDL verdict is evidence only when it survives three checks:

- **Cross-check**: `evalMatrix` and `evalReach` agree on the same
  `(model, world, formula)` for hundreds of randomized formulas and models. The
  suite generates random programs/formulas (depth-bounded, up to 8 worlds, 2
  propositions, 3 atomic programs) and asserts both engines return the identical
  truth value.
- **Exhaustive oracle**: known PDL validities are confirmed valid by brute-force
  enumeration of all frames up to small bounds — the K axiom, distribution
  `[a](p∧q) ↔ [a]p ∧ [a]q`, composition `[a;b]p ↔ [a][b]p`, union
  `[a∪b]p ↔ [a]p ∧ [b]p`, the star unroll `[a*]p → p`, the star induction axiom
  `[a*](p→[a]p) → (p→[a*]p)`, the test equivalence `[p?]q ↔ (p→q)`, and the
  diamond-star fixpoint `⟨a*⟩p ↔ p ∨ ⟨a⟩⟨a*⟩p`. Known *non*-validities
  (`p → [a*]p`, `[a]p → p`) are each handed a concrete countermodel found by the
  oracle.
- **Fail-closed replay**: `verifyClaim` replays a recorded verdict against both
  evaluators and fails if either evaluator diverges from the recorded
  expectation *or* if the two evaluators disagree. A verdict is accepted only
  when both independent engines reproduce it exactly; a wrong or wrongly-shaped
  expectation is rejected.

The test corpus is unit-tested beside the module (`src/modal/pdl.zig`), which is
the executable evidence referenced by the museum manifest.

## Limits

This exhibit is a complete executable contract for PDL on *finite* frames with
the regular-program fragment above. It does not claim:

- a parser (formulas are built via the arena builder),
- a Hilbert/Segerberg axiomatization or derived proof objects,
- converse programs (`α⁻¹`), intersection (`α∩β`), or hybrid PDL,
- determinism / well-foundedness / repeat-avoiding fragments,
- models larger than 16 worlds or more than 8 atomic programs per model,
- competition-scale model checking (the oracle is exact but bounded).

The semantics are exact for the named fragment; the boundary is the program
construct set and the finite-frame size, not soundness of the implementation.
