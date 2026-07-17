# logic-zig status

**Version:** 0.12.1  
**Last green:** golden **23/23**, external **DRAT verified**, `zig build test`

## Architecture

| Layer | Artifact |
|-------|----------|
| **Core library** | `logic` module |
| **Umbrella** | `logic-zig` |
| **Spin-offs** | agent · sat · hwmcc · cert · smt · ctl |
| **CI** | `.github/workflows/ci.yml` |

## Latest gates

```
./zig-out/bin/logic-hwmcc golden
# golden: 23/23 passed, 0 failed, 0 skipped

./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
# s UNSATISFIABLE / c external_drat=verified

./zig-out/bin/logic-sat portfolio file.cnf --proof
# internal_rup=ok + external_drat=verified when unsat
```

## Component matrix

| Component | Level |
|-----------|-------|
| CDCL + portfolio (6 configs, ramp, model validate, RUP) | unit-tested |
| External DRAT-trim | unit-tested when binary present |
| PDR + invariant export + cert verify | unit-tested |
| Fair multi-justice (round-robin + lasso + fairness) | unit-tested |
| AIGER golden fixtures (safe/unsafe/lasso/klive) | unit-tested |
| CTL / BV / agent session | unit-tested |

## Smoke

```sh
zig build test && zig build
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-agent session-demo
./zig-out/bin/logic-cert pdr-demo
```
