# Lean and Aristotle Oracle

`logic-zig` uses Lean as an external semantic oracle, not as a substitute for
the Zig implementation. The first oracle project formalizes the finite matrices
implemented in `src/logic/manyvalued.zig`.

## Trust boundary

The evidence chain is:

```text
Zig exhibit specification
    -> equivalent Lean definitions and named claims
    -> Lean kernel checks every proof term
    -> differential fixtures compare Zig decisions with the formalized contract
```

Aristotle may propose formalizations, proofs, refactors, and missing lemmas. Its
output is untrusted until the pinned Lean toolchain builds it. Generated code
must not contain `sorry`, `admit`, custom axioms, `unsafe` declarations, or a
changed theorem statement that makes the proof easier.

The oracle toolchain is pinned to the version recommended by the installed
Aristotle CLI. This pin is intentionally independent of the Zig compiler version.

## Local verification

```sh
cd lean
lake build
rg -n '\b(sorry|admit|axiom|unsafe)\b' . --glob '*.lean'
```

The second command is a source audit, not a substitute for Lean's kernel.

Blocking CI builds the oracle with Lean 4.28, performs that trust-escape audit,
and runs Lean's bundled `leanchecker` over the compiled environment. This is a
separate whole-environment checking pass, but it is not an
implementation-independent checker.

Nanoda remains a valuable independent Rust checker. Its current parser does not
accept the Lean 4.28 export stream, so it is tracked as an additional upstream
compatibility gate rather than being misreported as passing. Once compatible,
the nanoda gate should be restored alongside `leanchecker`.

## Aristotle workflow

Install the official CLI and provide its credential through the environment.
Never pass or commit the key itself.

```sh
scripts/aristotle-oracle.sh
aristotle list --limit 5
aristotle show PROJECT_ID
aristotle download PROJECT_ID --destination LOCAL_SCRATCH_PATH
```

Downloaded projects are reviewed outside the repository, diffed against the
submitted theorem statements, copied in through a normal branch, and required
to pass `lake build` plus the Zig gates before merge. Project and task identifiers
are operational account state and are not committed.

## Expansion order

1. Finite matrices and their separating countervaluations.
2. Dung extension semantics and exact acceptance.
3. Stable-model reduct semantics.
4. Reiter default extensions, AGM remainder sets, and circumscription.
5. SAT proof-checker semantics and circuit invariant obligations.
6. Translation/conservativity theorems between museum exhibits.

Lean establishes the mathematical contract. Zig must still provide validated
IRs, explicit resource behavior, executable evidence, high-performance engines,
and independent replay appropriate to its own APIs.
