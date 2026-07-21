# Finite AGM Belief-Base Change

## Formal identity

The exhibit implements syntax-sensitive change on a finite propositional belief
base `K`. Each belief is a small CNF. For target `phi`, the remainder family
`K perpendicular phi` contains exactly the inclusion-maximal sub-bases of `K`
that do not entail `phi`.

Partial-meet contraction selects remainder sets using one of three deterministic
policies:

- maxichoice keeps the first remainder in enumeration order;
- full meet intersects every remainder;
- cardinality intersects every maximum-cardinality remainder.

When `phi` is not entailed, vacuity keeps the full base. A tautological target
has no non-entailing remainder and invokes the AGM failure case, also preserving
the base. Revision by a literal cube uses the Levi identity: contract by its
negation, then add the cube explicitly.

## Decision and evidence contract

The engine admits at most 16 beliefs and enumerates every sub-base, so remainder
construction and all three selection policies terminate and are exact for the
declared representation. SAT entailment calls run without a conflict budget.

`verifyRemainders` rejects out-of-carrier and duplicate masks, independently
checks maximal non-entailment, and detects every omitted remainder by enumerating
the full sub-base lattice. `verifyContraction` replays vacuity, failure and the
chosen partial-meet policy from an exact remainder family. `verifyRevision`
reconstructs the Levi reduction and replays the retained-base result. Mutated
remainder and kept-set evidence fails closed.

The focused exhaustive test checks every sub-base of a representative four-belief
universe against three targets and all three selection policies. Canonical tests
cover success, inclusion, vacuity, tautological failure, cardinality selection,
full meet, and revision consistency.

## Limits

This is complete for the named finite belief-base representation, not for all AGM
theory change. It does not provide deductively closed theory objects, arbitrary
revision formulas, epistemic-entrenchment orderings, iterated-revision postulates,
belief merging, contraction histories, natural-language beliefs, or interchange
formats.
