# logic-zig status

**Version:** 0.14.0  
**Last green:** competition tracks · portfolio×9 · designs teeth · `TRUST_OK` · golden climb

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig sat-track corpus/bench/sat/simple_unsat.cnf --proof
./zig-out/bin/logic-zig sat-track corpus/bench/sat/simple_sat.cnf --quiet
./zig-out/bin/logic-zig sat-track corpus/bench/sat_comp/ph3.cnf --portfolio --budget 200000
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-hwmcc designs-demo
./zig-out/bin/logic-hwmcc track corpus/golden/aiger/stuck0.aag --cert
./zig-out/bin/logic-cert suite
./zig-out/bin/logic-agent warm-cold --structured --queries 120 --vars 12
```

## Evidence (v0.14)

| Gate | Result |
|------|--------|
| SAT track | Competition s/v + exit 10/20/0; `--proof` RUP; `--portfolio` |
| Portfolio | 9 configs (pure-first, glue-keep1, rephase, …) |
| DIMACS | Size caps, garbage reject, empty formula |
| HWMCC | PDR → k-induction → BMC; `--cert` / `--no-kind` |
| Designs | one-hot ring, Johnson, dual-rail, parity-never, multi-stuck kind |
| Cert suite | `logic-cert suite` multi-design battery |
| Solver | OOM ≠ UNSAT (`enqueue` error set); PDR init budget |

## Residuals (honest)

| Residual | Notes |
|----------|-------|
| Not Kissat / ABC / nuXmv parity | Competition *measurement*, not race wins |
| Full DRAT (vs RUP) | Internal RUP; external drat-trim when installed |
| IPASIR callbacks | `set_terminate` / `set_learn` documented no-ops |
| Heavy BMC unit tests | 6-bit counter bounds are demos, not Debug unit tests |

https://github.com/SMC17/logic-zig
