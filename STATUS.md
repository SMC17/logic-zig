# logic-zig status

**Version:** 0.16.0  
**Last green:** vivify · sat_hard scoreboard · SMT UF · ABC delta path · TRUST+UF

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig api-info
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat_comp --limit 15 --conflicts 200000
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat_hard --limit 8 --conflicts 300000 --industrial
./zig-out/bin/logic-zig abc-delta corpus/golden/aiger/stuck0.aag --frames 12
./zig-out/bin/logic-hwmcc golden
```

## Industrial program

See [docs/INDUSTRIAL.md](docs/INDUSTRIAL.md).

| Phase | Status |
|-------|--------|
| **0** Stable api/v1 | done |
| **1** Industrial SAT | vivify + scoreboard + sat_hard industrial mode |
| **2** MC + ABC path | `abc-delta` CLI · soft when ABC missing |
| **3** SMT | BV + **UF ground EUF** spine |
| **4** FOL | resolution skeleton |
| **5** CTL/BV | bounded / micro |

## Residuals (honest)

| Claim | Reality |
|-------|---------|
| Beat CaDiCaL PAR-2 always | **Not claimed** — measure per suite; often instance-speed WIN, PAR-2 lose |
| Full industrial SMT/FOL/ABC | Spines + paths; not Z3/Vampire/ABC parity |
| sat_hard full suite | Sampled with `--limit`; hard primes may unknown@budget |

https://github.com/SMC17/logic-zig
