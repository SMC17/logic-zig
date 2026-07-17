# logic-zig status

**Version:** 0.15.1  
**Last green:** industrial SAT scoreboard · deep preprocess · inprocess · CaDiCaL Δ

## Climb gates

```sh
zig build test && zig build
./zig-out/bin/logic-zig api-info
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig sat-scoreboard --dir corpus/bench/sat_comp --limit 20 --conflicts 200000
./zig-out/bin/logic-zig sat-track corpus/bench/sat/simple_unsat.cnf --proof
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-cert suite
```

## Industrial program

See **[docs/INDUSTRIAL.md](docs/INDUSTRIAL.md)**.

| Phase | Goal | Status |
|-------|------|--------|
| **0** Stable `api/v1` | version + capabilities | **done** (v0.15.0) |
| **1** Industrial SAT | preprocess + scoreboard vs CaDiCaL | **active** (v0.15.1) |
| **2** Industrial MC + ABC path | PDR depth + ABC Δ | engines exist · ABC interop probe |
| **3** Industrial SMT | BV + UF/array | facade ✓ · UF unsupported |
| **4** Full FOL prover | resolution → superposition | resolution skeleton ✓ |
| **5** CTL/BV polish | bounded CTL · BV ops | present · deepen |

## Evidence (v0.15 foundation)

| Gate | Target |
|------|--------|
| `api-info` | prints `1.0.0` + capability matrix |
| Preprocess | tautology/subsumption tests |
| FOL resolution | `P`/`¬P` and unify unsat |
| SMT facade | BV check · UF = unsupported (honest) |
| Trust (from 0.14) | DRAT / CaDiCaL / PDR / sequential |

## Residuals (honest — industrial not claimed)

| Residual | Notes |
|----------|-------|
| Not Kissat / CaDiCaL race parity | SAT industrial = approach, not win |
| Not ABC-class sequential | Interop + own PDR; no full ABC rewrite |
| Not Z3 / cvc5 | SMT is BV + stubs |
| Not Vampire / E | FOL is resolution skeleton |
| UF / arrays | capability bits **false** until real |
| API v1 | first freeze; spin-offs may still import internals |

https://github.com/SMC17/logic-zig
