# Trust layer

logic-zig separates a solver's answer, a checkable artifact, and evidence that
a checker accepted that artifact. `TRUST_OK` reports a finite fixture suite.
It does not authorize an agent action or certify an arbitrary future result.

## Result evidence

| Result | Certificate | Re-check |
|--------|-------------|----------|
| UNSAT | RUP/DRAT log | Internal `verifyRup`; independent `drat-trim` when explicitly requested |
| Safety proven (PDR/kind) | Inductive clauses | Initial-state inclusion, exclusion of bad states, inductiveness |
| Fair multi-justice finite | k-liveness / kind on thermometer | Named reduction and fixture status; retain engine limits |
| SAT | Model | `Cnf.checkModel` |

A certificate checked by another path in the same implementation is distinct
from a check by an independent tool. Neither establishes that a human's policy
was encoded correctly. Try the [deployment policy example](../examples/policy/README.md).

## Commands and exit statuses

```sh
./zig-out/bin/logic-zig trust-report
./zig-out/bin/logic-zig trust-report --json > ../trust-report.json
scripts/expect-status.sh 20 ./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-zig sat --file corpus/bench/sat/simple_unsat.cnf --check-drat
```

`trust-report` exits **0** only when every required axis has positive evidence
and no failures; **1** means refusal. `--json` emits one JSON document on stdout
on both pass and refusal. Usage errors exit **2**; execution errors may terminate
without a JSON report, so consumers must check both process status and content.

`logic-sat check-drat` uses competition status **20** for independently verified
UNSAT, **10** for SAT, and refuses an unverified UNSAT result with status **1**.
The umbrella `sat --file ... --check-drat` uses **0** for a completed result,
and also refuses missing or failed verification of UNSAT with **1**. Formula
mode rejects `--check-drat`; use `--file` to request independent checking.

External proof acceptance requires normal exit **0** and an exact `s VERIFIED`
status line. Negative, conflicting or incomplete statuses, diagnostic mentions
of `VERIFIED`, and abnormal or nonzero termination cannot establish verification.
The executable selected as checker is trusted to implement that protocol;
substituting a program that lies is outside this boundary.

## Required trust-report axes

| JSON `checks` key | Required evidence |
|-------------------|------------------|
| `drat` | Available; `verified > 0`; `failed == 0` |
| `cadical` | Available; `ran > 0`; `mismatches == 0` |
| `abc` | Available; **availability only**, not model-checking agreement |
| `pdr_certs` | `ok > 0`; `fail == 0` |
| `sequential` | `ok > 0`; `fail == 0` |
| `klive` | `ok > 0`; `fail == 0` |
| `agent` | `ok > 0`; `fail == 0` |
| `smt_uf` | `ok > 0`; `fail == 0` |

The JSON envelope has `schema_version: 1`, `status: "TRUST_OK" | "TRUST_FAIL"`,
`passed: boolean`, `scope: string`, and the `checks` object above. Counter values
are integers; availability values are booleans. Additive fields may appear.
Status is derived from evidence, not a separately supplied success flag.

An agent consuming a completed report should require exit 0, schema version 1,
`status == "TRUST_OK"`, and `passed == true`. Retain the report's scope when
presenting its result. Logs and hashes record evidence; they are not signatures
or attestations from a third party.

## Reproduce and inspect limits

Use the [portable trust demo](PORTABLE_TRUST_DEMO.md) for pinned checker setup.
The build applies the committed
[`drat-trim` exit-status patch](../scripts/patches/drat-trim-empty-clause-exit.patch)
to upstream revision `2e3b2dc0ecf938addbd779d42877b6ed69d9a985`. That revision prints
`s VERIFIED` for an input containing an empty clause but incorrectly exits 1;
the patch sets its successful status before returning. An unpatched checker
can therefore cause a deliberate refusal on that fixture under the strict gate.
Do not relax the gate to work around a failing checker.

Missing tools and zero-run axes block `TRUST_OK`. Golden-suite soft skips are
separate from this gate. Cross-compilation is compile evidence. Differential
agreement on selected inputs is not a proof of general correctness. See
[`STATUS.md`](../STATUS.md) for maturity, platforms and remaining work.
