# Executable Museum Contract

`logic-zig` aims to be **a Zig implementation of every branch of logic**. The
repository is organized as an executable museum: breadth is the product, while
every claim of completeness is local to a named formal system and mechanically
gated by evidence.

## What “complete” means

An exhibit is complete only relative to its published contract: formal identity,
syntax, semantics, calculus, automation boundary, proof objects, countermodels,
documentation, interoperability, decidability class, and known limitations.
Undecidable systems may have complete representations and complete calculi without
claiming a terminating decision procedure.

The source of truth is `src/taxonomy/exhibit.zig`. Run:

```sh
./zig-out/bin/logic-zig museum
```

The command prints every contracted exhibit followed by every registry system
that remains `catalog_only`. Registry breadth therefore stays visible without
granting implementation maturity or silently dropping branches from the museum.

Promotion is derived from dimension claims and their referenced evidence:

```text
cataloged -> specified -> kernel_complete -> automation_complete -> verified_exhibit
```

An absent test reference, specification, or evidence level makes the claim fail
closed. The older taxonomy registry remains the landscape index; it is not proof
that an implementation is complete.

## Three layers per exhibit

1. **Specification** defines the exact language and mathematical semantics.
2. **Kernel** evaluates models or checks derivations and certificates.
3. **Automation** searches for models, countermodels, proofs, or optimal answers.

Automation may be heuristic, bounded, or incomplete without weakening the meaning
of the specification or kernel.

## Admission rule

New catalog entries are welcome at any time. They cannot enter a stronger
collection until the manifest and executable gates support the promotion. Public
documentation and APIs must not translate `cataloged`, `partial`, `bounded`, or
`unknown` into `complete`, `verified`, or `false`.

## Frontier

The museum becomes a comparative research platform through translations,
conservativity checks, proof migration, weakest-logic classification, comparative
countermodels, mixed-logic boundaries, and machine-readable relationships between
systems. Shared infrastructure unifies evidence and interfaces, not semantics.
