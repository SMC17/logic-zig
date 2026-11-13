# Finite Logical Matrices Collection

## Shared contract

A finite logical matrix consists of a finite truth-value carrier, a designated
subset, and total tables for negation, conjunction, disjunction, and implication.
Consequence is preservation of designated values: `Γ ⊨ A` iff every valuation
designating every member of `Γ` also designates `A`.

For `n` values and `k` atoms there are exactly `n^k` valuations. The decision
procedure enumerates that finite set, so consequence and tautology are decidable
and the search is complete for formulas whose atom indices fit the declared
signature. Inputs with malformed tables, out-of-range outputs, more than eight
atoms, or formula atoms outside the signature fail closed as `invalid_input`.

Every invalid consequence carries a concrete countervaluation. Every valid result
records the exact expected valuation count; its checker validates the matrix and
formula, checks that count, and independently replays exhaustive consequence.
Countervaluations and exhaustive counts have mutation tests.

## K3: Strong Kleene logic

Values are false, indeterminate, and true. Only true is designated. Negation fixes
indeterminate; conjunction and disjunction are minimum and maximum in the Kleene
truth order; implication is material. Excluded middle and `p -> p` are not
tautologies, while explosion is vacuously valid because contradictions are never
designated.

## LP: Logic of Paradox

LP uses the same truth-function tables as K3 but designates both indeterminate/glut
and true. This makes excluded middle valid while explosion and material modus
ponens fail. The executable comparison demonstrates that consequence depends on
designation, not tables alone.

## FDE: First-Degree Entailment

Belnap–Dunn FDE uses four values: false, neither, both, and true, represented by
truth/falsity support pairs. Both and true are designated. Negation swaps false
and true and fixes neither/both. Meet and join use the truth order. Neither
excluded middle nor explosion is valid.

## Ł3: Three-valued Łukasiewicz logic

Ł3 uses values `0, 1/2, 1`, Kleene min/max conjunction/disjunction, involutive
negation, and implication `min(1, 1-a+b)`. `p -> p` is valid while excluded middle
and the tested contraction principle fail.

## Limits

These exhibits cover the exact finite matrices above. They do not claim continuum
fuzzy logic, arbitrary user-defined matrix parsing, quantified many-valued logic,
algebraic completeness theorems, relevance logics, or dialetheic metaphysics.
Those are separate museum contracts.
