# Propositional Normal Answer-Set Programming

## Formal identity

The exhibit implements finite propositional normal logic programs. A rule has
the form

```text
h <- p1, ..., pm, not n1, ..., not nk
```

where `h` is either one atom or absent. An absent head is an integrity
constraint. Atom identifiers range over the declared finite carrier.

For candidate interpretation `M`, the Gelfond-Lifschitz reduct removes every
headed rule whose negative body intersects `M`, then removes default-negated
literals from the remaining rules. `M` is stable exactly when it satisfies all
integrity constraints and equals the least model of that positive reduct.

## Decision and evidence contract

The decision procedure validates every head and body atom before shifting or
enumerating. The default contract admits at most 16 atoms; callers may explicitly
raise that limit only as far as the absolute supported bound of 20. It enumerates
all `2^n` interpretations and applies the reduct definition, so its returned list
is exact and the procedure terminates for every admitted input.

`verifyModels` treats a model list as evidence only after proving exactness. It
rejects out-of-carrier and duplicate interpretations, recomputes stability for
every interpretation, and compares expected membership with claimed membership.
Thus a nonempty result contains replayable stable-model witnesses, while an empty
result is replayable exhaustive evidence that the admitted program has no stable
model. Removing a model or duplicating one invalidates the evidence.

The focused corpus includes negative loops, constraints, stratification,
unfounded positive loops, and all 256 subsets of a representative eight-rule
universe over two atoms.

## Limits

This is not a complete implementation of ASP-Core-2. It has no variables,
grounder, disjunctive heads, classical negation, choice rules, aggregates, weak
constraints, optimization, parser, incremental control protocol, or clingo-scale
solver. Those require separate syntax, grounding, solving, proof, and
interoperability contracts.
