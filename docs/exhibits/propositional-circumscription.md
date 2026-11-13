# Finite Propositional Circumscription

## Formal identity

For propositional CNF theory `T`, atoms are partitioned into minimized atoms `P`,
fixed atoms `Q`, and all remaining varying atoms `Z`. A model `M` is `P`-minimal
when no model `M2` agrees with `M` on every fixed atom and makes a strict subset
of `M`'s true minimized atoms true. Varying atoms are unrestricted during this
comparison.

Circumscription entails a literal cube `phi` exactly when `phi` holds in every
`P`-minimal model of `T`. If `T` has no models, entailment is vacuously true.

## Decision and evidence contract

The admitted signature contains at most 16 minimized plus fixed atoms. Partition
atoms must be in the declared theory carrier and occur exactly once; query atoms
must also belong to that carrier. Invalid partitions, excessive signatures and
out-of-carrier queries return typed errors rather than assertions or Boolean
answers.

The engine enumerates every `(P,Q)` signature, uses complete SAT calls to retain
the satisfiable signatures, and performs exact subset minimization separately in
each `Q` class. Varying-atom completions remain symbolic until a query check.

A `Decision` records the exact minimal-signature family. For non-entailment it
also owns a minimal signature and a complete model of `T` that realizes that
signature and falsifies the query. `verifyDecision` reconstructs the exact
minimal family, rejects omissions and duplicates, validates the full model and
its signature, and replays query failure. An entailment decision is accepted only
after every exact minimal signature is conclusively checked for the absence of a
counterexample completion.

Random four-variable CNFs are differentially tested against a separate
full-assignment minimal-model oracle. Canonical tests cover abnormality
minimization, exceptions, disjunctive minimization, malformed partitions and
mutated evidence.

## Limits

This exhibit does not implement first-order or predicate circumscription,
formula-valued queries beyond cubes, prioritized, parallel, nested or varied
circumscription policies, circumscription-to-SO translations, external formats,
or an industrial minimal-model engine.
