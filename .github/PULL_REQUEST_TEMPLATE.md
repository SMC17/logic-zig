## Problem

What semantic, correctness, performance, interoperability, or documentation gap
does this change close?

## Contract and scope

- Named logic/system:
- Supported fragment:
- Completeness boundary:
- Deliberately unsupported behavior:

## Evidence

- [ ] A failing or separating test existed before the fix where applicable.
- [ ] Models/countermodels/proofs are replayed rather than trusted as Booleans.
- [ ] `unknown`, unsupported input, and resource exhaustion fail closed.
- [ ] Mutation or negative tests reject corrupted evidence.
- [ ] `zig build test` passes.
- [ ] `zig build` passes.
- [ ] Documentation and `[Unreleased]` changelog match the executable state.
- [ ] No secrets, account identifiers, private paths, or generated service state are committed.

Commands and results:

```text
paste concise reproducible evidence here
```

## Type I / Type II review

- False-positive risk: what could this change incorrectly promote as proved?
- False-negative risk: what real behavior or capability could the tests miss?
- Not measured:
