# logic-zig status

**Version:** 0.13.1  
**Last green:** `TRUST_OK` · golden **51/51** · sequential ok=6 · track `--cert` verified

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-hwmcc designs-demo
./zig-out/bin/logic-hwmcc track corpus/golden/aiger/stuck0.aag --cert
./zig-out/bin/logic-agent warm-cold --structured --queries 120 --vars 12
./zig-out/bin/logic-agent stress --queries 1000 --vars 12
```

## Evidence (latest)

| Gate | Result |
|------|--------|
| Trust | DRAT 5/0, CaDiCaL 0 mismatch, PDR certs 3, sequential 6 |
| Golden | 51/51 |
| Cert track | `source=pdr clauses=1 verified=true` |
| Designs | counter5 30/31, multi-stuck5 cert, mutex constraint |

https://github.com/SMC17/logic-zig
