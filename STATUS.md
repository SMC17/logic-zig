# logic-zig status

Last green: 2026-07-16 (`zig build test`; `zig build -Doptimize=ReleaseFast`;
`correctness-suite`; `bench-comp`; external **drat-trim**)

## Win scoreboard (v0.10)

| Axis | Result |
|---|---|
| correctness (fuzz/dimacs/RUP/cores/Δ-CaDiCaL) | **PASS** |
| **external DRAT-trim** | **PASS** (unit + fuzz + up to 40 comp UNSATs) |
| par2 smoke (library) | **WIN** |
| par2 fair (process) | **WIN** |
| par2 medium | **WIN** |
| multishot QPS | **WIN** (~1e3–1e5× cold CaDiCaL) |
| hwmcc micro | **PASS** |
| embed (IPASIR `.so` + CLI) | **WIN** |
| competition correctness (94 CNFs, 0 mismatches) | **PASS** |
| competition DRAT sample | **PASS** (30 verified, 0 failed) |
| competition PAR-2 speed | **LOSE** (CaDiCaL leads heavy tail; measured) |
| competition instance majority | **LOSE** (~41 vs 53 faster) |

```sh
gcc -O2 -o third_party/drat-trim/drat-trim third_party/cadical/test/cnf/drat-trim.c
zig build test && zig build -Doptimize=ReleaseFast && zig build lib
./zig-out/bin/logic-zig win-report --comp
./zig-out/bin/logic-zig bench-comp
./zig-out/bin/logic-zig sat --file corpus/simple_unsat.cnf --check-drat
```

## What shipped this wave

- `corpus/bench/sat_comp/` (~75 CNFs): CaDiCaL unit tests + generated 3-SAT
- `corpus/bench/sat_hard/` stretch set (add64, large primes, …)
- `src/sat/drat_external.zig` — discover + run vendored **drat-trim**
- `src/track/comp_bench.zig` — competition PAR-2 + DRAT sample
- CLI: `bench-comp`, `sat --check-drat`, `sat --dump-proof PATH`, `win-report --comp`
- Solver: watch/trail pre-size, O(trail) `isLocked`, free-var `orig_cnf` fix (prior)

## Residuals (honest)

| Residual | Status |
|---|---|
| Beat CaDiCaL on industrial CDCL heavy tails | Open — `sat_hard` documents the gap |
| Full DRAT on every competition UNSAT | Sampled (cap 40) for runtime |
| Strip/size contest | Unstripped ReleaseFast not claimed |
| SAT Race submission packaging | Not done |

## Corpora

See [`corpus/bench/README.md`](corpus/bench/README.md).
