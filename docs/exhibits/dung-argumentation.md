# Dung Abstract Argumentation

## Formal identity

An abstract argumentation framework is a finite directed graph `AF = (A, R)`.
Elements of `A` are opaque arguments and `(a,b) in R` means that `a` attacks
`b`. The implementation uses argument identifiers `0..n-1` and rejects attack
endpoints outside that carrier.

For a set `S` of arguments:

- `S` is conflict-free when no member attacks a member;
- `S` defends `a` when every attacker of `a` is attacked by some member of `S`;
- `S` is admissible when it is conflict-free and defends all its members;
- `S` is complete when it is admissible and contains every argument it defends;
- the grounded extension is the least fixed point of the defense characteristic
  function;
- `S` is stable when it is conflict-free and attacks every argument outside `S`;
- `S` is preferred when it is inclusion-maximal among admissible sets.

Credulous acceptance means membership in at least one extension. Skeptical
acceptance means membership in every extension. Following the module's explicit
engineering convention, skeptical acceptance is false when a semantics has no
extensions; this matters for stable semantics.

## Decision and evidence contract

For frameworks with at most 20 arguments, extension search enumerates all `2^n`
subsets. Grounded semantics additionally has a direct least-fixed-point
computation. Preferred candidates are filtered by exact inclusion maximality.
Consequently, the shipped procedures terminate and are complete for the named
finite semantics, although their worst-case running time is exponential.

An extension result is evidence only when `verifyExtensions` confirms both sides
of the claim: every listed set satisfies the selected semantics and no satisfying
set was omitted. Duplicate and out-of-carrier sets are rejected. An acceptance
decision carries the exact extension evidence used for the answer;
`verifyAcceptance` first rechecks that evidence and then recomputes the selected
credulous or skeptical predicate.

The test corpus exhausts every one of the 512 attack relations on three arguments,
under all five semantics and both acceptance modes. It also mutates evidence and
checks malformed frameworks and out-of-range queries fail closed.

## Limits

This exhibit does not claim ICCMA-scale performance, an ICCMA interchange parser,
semi-stable, stage, ideal, value-based, bipolar, structured, probabilistic, or
dynamic argumentation. It is a complete executable contract for the finite Dung
semantics named above, not for every extension of abstract argumentation theory.
