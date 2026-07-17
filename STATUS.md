# logic-zig status

**Version:** 0.12.2  
**Last green:** golden **30/30** · DRAT fuzz **verified=9 failed=0** · portfolio hard **0 failed**

## Gates

```sh
zig build test && zig build
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-sat drat-fuzz --iters 15 --vars 5
./zig-out/bin/logic-sat hard --dir corpus/bench/sat --limit 8 --conflicts 80000
# optional: --dir corpus/bench/sat_hard --limit 5 --conflicts 500000
```

## Spin-offs

| Binary | Commands |
|--------|----------|
| `logic-sat` | solve, portfolio, check-drat, **drat-fuzz**, **hard** |
| `logic-hwmcc` | track, klive, **golden** |
| `logic-agent` | multishot, session-demo |
| `logic-cert` | unsat-demo, klive-demo, pdr-demo |

## Stack

Core library + 6 flagships · CI · DRAT-trim · portfolio · fair multi-justice · AIGER goldens · certs · CTL · BV
