# Frozen benchmark corpus

## `sat/`

39 small/medium DIMACS CNFs (CaDiCaL unit tests + local smoke). Used by:

```sh
./zig-out/bin/logic-zig bench-suite
./zig-out/bin/logic-zig bench-suite --fair   # process vs process
./zig-out/bin/logic-zig correctness-suite
```

## Protocol

| Mode | Internal | External | Claims |
|---|---|---|---|
| default | in-process CDCL | CaDiCaL subprocess | embeddable library latency |
| `--fair` | `logic-zig sat-track` subprocess | CaDiCaL subprocess | comparable single-shot wall time |
| multishot | live assume/solve | cold CaDiCaL per query | incremental IPASIR axis |
| correctness | models + RUP + Δ-CaDiCaL | CaDiCaL | agreement / validation |

PAR-2: sum of solve times; unknown/timeout counts as `2 * timeout_s`.

Do not extend this suite silently when claiming a win — freeze the file list with the result.
