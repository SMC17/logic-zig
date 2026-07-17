# Frozen benchmark corpus

## Layout

| Dir | Contents | Role |
|---|---|---|
| `sat/` | 39 small CNFs | smoke correctness + PAR-2 |
| `sat_medium/` | 15 medium CaDiCaL unit CNFs | mid-tier PAR-2 |
| `sat_comp/` | ~75 competition-slice CNFs | match + external DRAT + speed |
| `sat_hard/` | stretch (add64, large primes, …) | aspirational; not required to win |
| `generated/` | random 3-SAT seeds | repro generators |
| `hwmcc/` | AIGER micro | sequential engines |

```sh
# full scoreboard including competition slice + external DRAT-trim
./zig-out/bin/logic-zig win-report --comp

# competition only
./zig-out/bin/logic-zig bench-comp --timeout 3 --max-conflicts 300000

# dump + external check one proof
./zig-out/bin/logic-zig sat --file corpus/simple_unsat.cnf --check-drat --dump-proof /tmp/p.drat
```

## External DRAT-trim

Built from CaDiCaL’s bundled checker:

```sh
gcc -O2 -o third_party/drat-trim/drat-trim third_party/cadical/test/cnf/drat-trim.c
# or LOGIC_ZIG_DRAT_TRIM=/path/to/drat-trim
```

## Protocol

| Mode | Internal | External | Claim |
|---|---|---|---|
| default PAR-2 | in-process CDCL | CaDiCaL subprocess | library latency |
| `--fair` | `sat-track` subprocess | CaDiCaL subprocess | single-shot wall |
| multishot | live assume/solve | cold CaDiCaL/query | IPASIR embed |
| DRAT | our RUP/DRAT log | `drat-trim` | certifying UNSAT |
| competition | match + PAR-2 + DRAT sample | CaDiCaL + drat-trim | slice scoreboard |

PAR-2: sum of times; unknown/timeout = `2 * timeout_s`.

**Speed honesty:** on `sat_hard` and heavy industrial CDCL, CaDiCaL still leads.
Required wins = correctness agreement + external DRAT + multishot + smoke PAR-2.
Competition **speed** PAR-2 is reported; lose is a valid measured outcome.
