# Try a solver result with an independent proof check

Use Zig 0.16.0. Native macOS ARM64 and Linux ARM64 were exercised for this
preview. C/C++ build tools, make, Git, and Python 3 are needed for the external
checker build and refusal regression tests. The checker script downloads pinned
upstream source revisions; it does not reuse or overwrite existing third_party
checkout directories.

From a fresh checkout:

```sh
zig build test
zig build
./zig-out/bin/logic-zig doctor
scripts/build-checkers.sh
python3 tests/host_gate_smoke.py
scripts/expect-status.sh 20 ./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
./zig-out/bin/logic-zig trust-report
```

`check-drat` uses SAT competition status 20 for a verified UNSAT result. The
wrapper asserts that exact status. `trust-report` must finish with `TRUST_OK`
after positive evidence on every required axis. A missing checker or an
inconclusive response is a refusal, not a successful independent check.

Measured on 11 November 2026 with Zig 0.16.0:

| Runtime | Tests | Independent trust run |
| --- | --- | --- |
| macOS ARM64 | 391/391 | DRAT 5 verified; CaDiCaL 25 comparisons, zero mismatches; TRUST_OK |
| Ubuntu 24.04 ARM64 | 391/391 | DRAT 5 verified; CaDiCaL 25 comparisons, zero mismatches; TRUST_OK |

Linux x86-64 also cross-compiles, but that is not an x86-64 runtime result.
ABC is available in the recorded trust run. Its optional delta comparison
returned unknown; no independent ABC model-checking agreement is claimed.
The trust result exercises a finite suite, not the truth of every result from
every engine. Read STATUS.md for the system-by-system maturity and residuals.
Hosted Actions could not start because of an account billing restriction; the
measurements above come from the native local runtimes, not hosted CI.

If this fails, open an issue with the toolchain, operating system, input,
command, expected status and actual output. Do not include secrets or private
workstation files.

On Linux, [record the checked task in zag](RECORDED_PROOF_DEMO.md) and verify
the command history and stored output objects.
