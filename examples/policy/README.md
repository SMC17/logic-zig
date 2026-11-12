# Can deployment happen without approval?

This example turns a small policy question into explicit constraints, exports
an UNSAT proof, and checks it with a separate executable. Removing the approval
rule makes the same question satisfiable; the old proof must then be rejected.

| Variable | Meaning |
|----------|---------|
| 1 | Deployment occurs |
| 2 | Human approval exists |
| 3 | Checks passed |

[`blocked.cnf`](blocked.cnf) encodes `deploy -> approval` and
`deploy -> checks_passed`, then asks for `deploy AND NOT approval`.
There is no satisfying assignment. [`weakened.cnf`](weakened.cnf) removes
`deploy -> approval`. Now deployment without approval is possible, for example
with variables `1=true, 2=false, 3=true`.

## Run with real tools

Use Zig 0.16.0 and Python 3. Build the CLIs and the pinned checkers from a fresh
checkout, as described in the [portable trust demo](../../docs/PORTABLE_TRUST_DEMO.md):

```sh
zig build
scripts/build-checkers.sh
python3 tools/policy_demo.py --out ../policy-evidence
```

The runner performs four checks: proof export, independent proof acceptance,
a SAT result for the weakened policy, and rejection of the original proof
against that changed input. It exits 0 only when all four pass. Existing output
directories are refused. An existing checker can be selected with `--checker`
or `LOGIC_ZIG_DRAT_TRIM`; nothing is installed by the runner.

The output contains both CNFs, `blocked.drat`, four logs, `receipt.json`, and
`SHA256SUMS`. The receipt records the source commit, whether the source tree
was dirty, the runtime platform, binary hashes, input/proof/log hashes and
actual command outcomes. It records the runner hash as well. Hashes detect
changes relative to that receipt; they do not establish the identity or
honesty of whoever produced it.

Replay the proof independently of the runner, from the evidence directory:

```sh
/path/to/drat-trim blocked.cnf blocked.drat
/path/to/drat-trim weakened.cnf blocked.drat
```

The first command must exit 0 with `s VERIFIED`. The second must fail with
`s NOT VERIFIED`. Check the process status as well as its text. `blocked.drat`
may contain only the empty clause: this tiny contradictory policy is already
refutable by unit propagation. No large-instance performance claim follows.

## Integration boundary

In an agent runtime, trusted application code must translate an actual proposed
action and policy into the constraints, bind any proof to those exact inputs,
and enforce the resulting decision before acting. This example checks two
encodings; it does not connect to a deployment system, authenticate approval,
or prove that a natural-language policy was translated faithfully.

The [JSON trust report](../../docs/TRUST.md) is a separate health check of the
finite fixture suite. Its success does not replace checking a particular
action's inputs and proof.
