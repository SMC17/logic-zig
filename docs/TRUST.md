# Trust layer

Every serious result in logic-zig is either **certified** or **explicitly uncertified**.

## What we certify

| Result | Certificate | Re-check |
|--------|-------------|----------|
| UNSAT | RUP additions/deletions with explicit assumption context | Search-independent `verifyRup` + external `drat-trim` |
| Safety proven (PDR) | Inductive clauses | `Init⇒I`, `I⇒¬Bad`, `I∧T⇒I′`; every query conclusively UNSAT |
| Fair multi-justice finite | k-liveness / kind on thermometer | Status + k in text cert |
| SAT | Model | `Cnf.checkModel` |

## Commands

```sh
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig check-rup formula.cnf proof.rup
./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-sat drat-fuzz --iters 30 --vars 6
./zig-out/bin/logic-cert pdr-demo
./zig-out/bin/logic-hwmcc stack
```

## Trust report fields

- **drat**: external trim verified/failed counts  
- **serialized_rup**: producer bytes checked by the search-independent native checker
- **cadical**: differential mismatches on random CNFs  
- **abc**: presence only (optional baseline)  
- **pdr_certs**: proven designs with re-verified invariants  
- **sequential**: counter/shift BMC teeth  
- **klive**: multi-justice finite vs non-false-prove  

`TRUST_OK` requires DRAT-trim with at least one verified proof, CaDiCaL with at
least one completed comparison, ABC availability, and zero DRAT, differential,
certificate, sequential, liveness, agent, or SMT failures.

## Honest limits

External tools may be missing (`drat-trim`, CaDiCaL, ABC). Missing tools are
reported and prevent `TRUST_OK`; soft-skips remain possible in non-trust golden
tests. The internal checker is independent of CDCL search but is not formally
verified, and the current format checks RUP additions rather than full RAT/FRAT/LRAT.
