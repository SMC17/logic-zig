# Frozen benchmark corpus

## Layout

| Dir | Contents |
|---|---|
| `sat/` | 39 small CNFs (primary correctness + PAR-2) |
| `sat_medium/` | 15 harder CaDiCaL unit CNFs (add16/32, primes, factors, …) |
| `hwmcc/` | AIGER micro-instances for sequential engines |

```sh
./zig-out/bin/logic-zig win-report                 # full scoreboard
./zig-out/bin/logic-zig bench-suite
./zig-out/bin/logic-zig bench-suite --fair
./zig-out/bin/logic-zig bench-suite --dir corpus/bench/sat_medium --timeout 10
./zig-out/bin/logic-zig hwmcc-bench
./zig-out/bin/logic-zig correctness-suite
```

## Protocol

| Mode | Internal | External | Claims |
|---|---|---|---|
| default | in-process CDCL | CaDiCaL subprocess | embeddable library latency |
| `--fair` | `logic-zig sat-track` subprocess | CaDiCaL subprocess | comparable single-shot wall time |
| multishot | live assume/solve | cold CaDiCaL per query | incremental IPASIR axis |
| correctness | models + RUP + Δ-CaDiCaL | CaDiCaL | agreement / validation |
| hwmcc-bench | PDR/BMC/kind on demos | (oracle-free status) | sequential smoke + timing |

PAR-2: sum of solve times; unknown/timeout counts as `2 * timeout_s`.

Do not extend suites silently when claiming a win — freeze the file list with the result.
