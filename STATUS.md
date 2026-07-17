# logic-zig status

**Version:** 0.13.0  
**Last green:** `TRUST_OK` · golden **48/48** · agent stress 500q · IPASIR consumer OK

## Mountains climbed this release

| # | Claim | Gate |
|---|--------|------|
| 1 | **Trust layer** | `trust-report` → DRAT verified, CaDiCaL mismatches=0, PDR certs ok |
| 2 | **Agent-native** | `logic-agent stress` / `warm-cold` / session / IPASIR consumer |
| 3 | **Sequential teeth** | designs: 3–4bit counter BMC, multi-stuck PDR certs, fair multi |

## Commands

```sh
zig build test && zig build
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-agent stress --queries 1000 --vars 12
./zig-out/bin/logic-agent warm-cold --queries 200 --vars 10
./zig-out/bin/ipasir-consumer
./zig-out/bin/logic-hwmcc stack
```

## Docs

- [docs/TRUST.md](docs/TRUST.md)
- [docs/AGENT.md](docs/AGENT.md)
- [docs/PRODUCTS.md](docs/PRODUCTS.md)

## Repo

https://github.com/SMC17/logic-zig
