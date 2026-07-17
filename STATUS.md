# logic-zig status

**Version:** 0.12.3  
**Last green:** golden **44/44** · `STACK_OK` · DRAT fuzz clean · sat_hard sample · `DOCTOR_OK`

## One-liner stack

```sh
zig build test && zig build
./zig-out/bin/logic-hwmcc stack
./zig-out/bin/logic-sat drat-fuzz --iters 15 --vars 5
./zig-out/bin/logic-sat hard --dir corpus/bench/sat --limit 12
./zig-out/bin/logic-sat hard --dir corpus/bench/sat_hard --limit 3 --conflicts 150000
./zig-out/bin/logic-zig doctor
```

## Flagships

| Binary | Depth |
|--------|--------|
| `logic-hwmcc` | golden, stack, fair-demo, track, klive |
| `logic-sat` | portfolio, check-drat, drat-fuzz, hard |
| `logic-agent` | session-demo, multishot |
| `logic-cert` | pdr-demo, klive-demo |
| `logic-smt` / `logic-ctl` | demos |

## Repo

https://github.com/SMC17/logic-zig
