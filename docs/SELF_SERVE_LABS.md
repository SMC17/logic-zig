# Choose one reasoning task

These entry points share the logic-zig core. They are separate tasks, not
separate claims of production maturity. No model service or API key is needed.

| Task | Entry point | What a successful run establishes |
| --- | --- | --- |
| Solve a tiny propositional instance | logic-sat, the committed SAT fixtures | A result on the selected instance; independent proof checking is separate |
| Explore hardware model-checking fixtures | logic-hwmcc and its documented golden task | Finite AIGER/model-checking examples, under the named engine's limits |
| Exercise local certificates | `logic-cert suite` | The local fixture suite accepts/rejects its test certificates |
| Try bit-vector arithmetic | `logic-smt demo-add` | The bit-blasted addition fixture computes its expected outcome |
| Explore branching-time properties | `logic-ctl demo` | The bounded CTL fixture runs, not full symbolic CTL completeness |
| Connect a checked task to a recorded workspace | [zag example](RECORDED_PROOF_DEMO.md) | Recorded command/output integrity, distinct from solver truth |

## Build and package

With Zig 0.16.0:

```sh
zig build test -Doptimize=ReleaseSafe --summary all
zig build -Doptimize=ReleaseSafe
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-cert suite
./zig-out/bin/logic-smt demo-add
./zig-out/bin/logic-ctl demo
```

For a clean-source pack, use Python 3.12 or newer and the native `strip` tool:

```sh
python3 tools/selfserve.py selfserve.json --repo . --out ../logic-zig-pack
```

The tool extracts committed HEAD into a fresh directory. It runs the unit suite
and selected tasks there, strips binary debug symbols, then writes source,
seven CLIs, command logs, result.json, TRY.md and SHA256SUMS. A failure, timeout
or missing unit-test evidence prevents PASS. Untracked checker installs cannot
make this acceptance task pass.

External checker binaries are not included. To obtain independently checked
UNSAT results, follow [the portable trust demo](PORTABLE_TRUST_DEMO.md). Missing
checking still refuses TRUST_OK. Preserve STATUS.md's per-engine boundaries.

The self-serve workflow runs on pull requests, main updates, manual requests
and a monthly schedule. A maintainer-pushed `selfserve-*` tag can publish a
prerelease after both native Linux and macOS jobs pass. It does not create a
tag, claim benchmark parity, or silently make research engines production-ready.
Hosted execution remains blocked until the account billing restriction clears.
