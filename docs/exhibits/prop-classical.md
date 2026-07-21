# Classical Propositional Logic Exhibit

## Formal identity

This exhibit implements finite classical propositional logic with Boolean truth
values `{false, true}` and the connectives constant, negation, conjunction,
disjunction, implication, biconditional, and exclusive disjunction. A valuation
maps every atomic proposition to exactly one Boolean value. Formula meaning is the
standard compositional truth function.

The decision problem is satisfiability. Validity is decided by testing the
negation for unsatisfiability; equivalence is validity of a biconditional.

## Syntax and semantics

`ExprPool` is the typed arena representation. `parse/prop.zig` parses the concrete
language, and `ExprPool.eval` is the executable semantic kernel. Returned SAT
models are replayed against both the generated CNF and the original expression.
An invalid or partial replay is an error, not a satisfying result.

## Calculus and automation

Formulas are converted to equisatisfiable CNF with a Tseitin transformation. The
CDCL procedure uses watched literals, conflict analysis, learned clauses,
backjumping, restarts, and finite resource limits. With unlimited limits it is a
decision procedure for finite propositional formulas. A limited run may return
`unknown`; adapters may not translate that result to SAT, UNSAT, validity, or
invalidity.

Preprocessing and incremental operation are separate contracts. Conflict budgets
and reported statistics are per call. Assumption cores carry tri-state minimality
and uniqueness evidence.

## Evidence

SAT results contain a total replayable valuation. UNSAT results on the direct
proof-producing path contain RUP clause additions/deletions. Assumption-dependent
proofs serialize an ordered `a ... 0` assumption context.

`proof/rup_checker.zig` parses strict DIMACS and serialized proof bytes without
importing the solver, producer proof object, preprocessing, or CDCL structures. It
replays RUP by its own unit-propagation implementation, checks deletions, requires a
final empty addition, and rejects malformed inputs. Producer-to-byte-to-checker
tests cover ordinary and assumption proofs; mutation tests cover invalid additions,
unknown deletions, missing assumption contexts, integer/range errors, unterminated
clauses, and header/count mismatches.

The trust workflow also checks generated proofs with external `drat-trim` and
differentially compares decisions with CaDiCaL.

## Completeness contract

Within this exhibit’s scope:

- syntax representation and evaluation are complete for the listed connectives;
- SAT/validity/equivalence are decidable;
- unlimited CDCL search is complete;
- every reported SAT result has a replayed model;
- every proof-producing UNSAT result has serialized RUP evidence accepted by the
  search-independent checker;
- bounded or interrupted computations remain `unknown`.

This justifies `verified_exhibit` at the repository’s `audited` proof level. It is
not a claim of formal verification.

## Explicit limitations

- The independent checker is implemented and adversarially tested, not proved in a
  proof assistant.
- The native serialized checker supports RUP additions and exact deletions, not
  arbitrary RAT, FRAT, or LRAT inputs.
- External `drat-trim` remains a separate trust anchor for ordinary DRAT streams.
- Performance is not at CaDiCaL/Kissat parity; the correctness and performance
  verdicts are deliberately separate.
- Proof reconstruction across every optional preprocessing transformation is not
  included. The proof-complete contract applies to the direct proof-producing
  path; a future transformation ledger must extend it to aggressive preprocessing.

## Primary executable evidence

```text
src/ir/expr.zig
src/pass/tseitin.zig
src/sat/solver.zig
src/sat/drat.zig
src/proof/rup_checker.zig
tests/integration_test.zig
```

Run `zig build test`, `logic-zig trust-report`, and `logic-zig museum` from the
repository root.
