# Golden fixtures

Built-in golden cases run without this directory (`logic.golden.runBuiltin` /
`logic-hwmcc golden`). Add file-based fixtures here for CI expansion:

| File | Expect |
|------|--------|
| (builtin) unit CNF unsat/sat | pass |
| (builtin) PDR stuck0 | proven |
| (builtin) BMC counter | violated |
| (builtin) AIGER and2 parse | ok |

Future: JSONL manifest `manifest.jsonl` with `path`, `kind`, `expect`.
