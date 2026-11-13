# Finite Propositional Reiter Default Logic

## Formal identity

A default theory is `(W,D)`, where `W` is propositional CNF and each default in
`D` has a cube prerequisite, zero or more cube justifications, and a cube
consequent. Empty prerequisites mean truth; an empty justification list imposes
no consistency obligation.

The exhibit represents an extension by its generating set `GD`. A candidate is
accepted exactly when:

1. every selected default can be reached by iterated prerequisite entailment
   from `W` and previously fired consequents, excluding self-supporting cycles;
2. every selected justification is consistent with the final theory
   `W` plus all selected consequents; and
3. no unselected default is applicable in that final theory.

Entailment and consistency reduce to complete SAT calls with no conflict budget.
An inconsistent `W` receives the standard degenerate deductive closure; defaults
whose justifications are inconsistent with it cannot generate.

## Decision and evidence contract

The engine enumerates all `2^|D|` generating sets and therefore decides the
admitted finite fragment. The public boundary rejects a caller limit above 20,
theories exceeding the chosen limit, and generating-set length mismatches.

`verifyExtensions` replays exact extension evidence. It rejects malformed and
duplicate generating sets, checks every claimed set against groundedness,
justification consistency and stability, and enumerates the entire generating-set
space to detect omissions. Consequently, an empty result is evidence that the
admitted theory has no extension, not merely failure to find one. Credulous and
skeptical cube queries are meaningful relative to this verified extension set;
the engineering convention returns false for either mode when no extension
exists rather than silently using vacuous skeptical truth.

Tests cover Tweety with and without an exception, the Nixon diamond,
extensionless defaults, self-support rejection, chained defaults, inconsistent
facts, evidence mutation, malformed limits, and every subset of a representative
four-default universe.

## Limits

This contract does not include arbitrary formula components, first-order open
defaults, priorities, constrained or justified variants, autoepistemic logic,
parsers, proof interchange, incremental theory updates, or an industrial
nonmonotonic solver. Each is a separate museum expansion.
