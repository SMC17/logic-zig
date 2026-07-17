# Edge corpus — extreme tiny fixtures

Hand-written minimal CNF and AIGER files for parser / solver / MC edge cases.
Not a competition suite — intended for differential smoke tests vs CaDiCaL / ABC
when those tools are present.

## CNF (`*.cnf`)

| File | Expect (coarse) | Notes |
|------|-----------------|-------|
| `empty.cnf` | SAT | 0 vars, 0 clauses |
| `empty_clause.cnf` | UNSAT | single empty clause |
| `unit_clash.cnf` | UNSAT | `1` and `-1` units |
| `unit_sat.cnf` | SAT | single unit |
| `all_tautology.cnf` | SAT | only tautological clauses |
| `pure_positive.cnf` | SAT | pure-literal friendly |
| `sparse_high_var.cnf` | SAT | max-var 1000, 2 clauses |
| `long_clause.cnf` | SAT | 16-lit clause |
| `xor2.cnf` | SAT | 2-var XOR |
| `ph2.cnf` | UNSAT | 2 pigeons / 1 hole |
| `dup_lits.cnf` | SAT | duplicate lits in clauses |

## AIGER (`*.aag`)

| File | Notes |
|------|-------|
| `empty.aag` | zero I/O/L/A |
| `const0.aag` / `const1.aag` | constant PO |
| `passthrough.aag` | combinational buffer |
| `and2.aag` | y = a ∧ b |
| `self_and.aag` | y = a ∧ a |
| `nor2.aag` | y = ¬a ∧ ¬b |
| `latch0.aag` / `latch1.aag` | stuck latches |
| `toggle.aag` | q′ = ¬q |

## Differential smoke (optional)

```sh
# SAT vs CaDiCaL (from repo root)
for f in corpus/edge/*.cnf; do
  echo "== $f =="
  third_party/cadical/build/cadical "$f" | tail -3
done

# ABC (if built)
# third_party/abc/abc -c 'read_aiger corpus/edge/and2.aag; print_stats'
```
