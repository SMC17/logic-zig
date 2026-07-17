# Golden fixtures

Built-in golden cases run without this directory (`logic.golden.runBuiltin` /
`logic-hwmcc golden`). Add file-based fixtures here for CI expansion:

| File | Expect |
|------|--------|
| (builtin) unit CNF unsat/sat | pass |
| (builtin) PDR stuck0 | proven |
| (builtin) BMC counter | violated |
| (builtin) empty-bad / multi-bad / constraint / dual-rail | pass |
| (builtin) AIGER and2 parse | ok |
| `empty_bad.aag` | safe (vacuous) |
| `multi_bad.aag` | unsafe (OR of props) |
| `constraint_safe.aag` | safe under C |
| `init_conflict.aag` | safe (vacuous) |

JSONL manifest `manifest.jsonl` with `path`, `kind`, `expect`.
