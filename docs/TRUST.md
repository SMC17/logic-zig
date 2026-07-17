# Trust layer

Every serious result in logic-zig is either **certified** or **explicitly uncertified**.

## What we certify

| Result | Certificate | Re-check |
|--------|-------------|----------|
| UNSAT | RUP/DRAT log | Internal `verifyRup` + external `drat-trim` when present |
| Safety proven (PDR/kind) | Inductive clauses | `Init∧I∧bad` unsat, `Init⇒I`, relative inductiveness |
| Fair multi-justice finite | k-liveness / kind on thermometer | Status + k in text cert |
| SAT | Model | `Cnf.checkModel` |

## Commands

```sh
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-sat drat-fuzz --iters 30 --vars 6
./zig-out/bin/logic-cert pdr-demo
./zig-out/bin/logic-hwmcc stack
```

## Trust report fields

- **drat**: external trim verified/failed counts  
- **cadical**: differential mismatches on random CNFs  
- **abc**: presence only (optional baseline)  
- **pdr_certs**: proven designs with re-verified invariants  
- **sequential**: counter/shift BMC teeth  
- **klive**: multi-justice finite vs non-false-prove  

`TRUST_OK` means no failed DRAT, no CaDiCaL mismatches, no cert/seq/klive failures.

## Honest limits

External tools may be missing (`drat-trim`, CaDiCaL, ABC). Missing tools are reported, not silently treated as pass — except soft-skips in golden when unavailable.
