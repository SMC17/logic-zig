# Record a proof-checking task in zag

This Linux example composes two existing tools. logic-zig runs the independent
checks; zag records the command and output, then verifies its event chain and
stored output objects. Recording does not independently prove the solver's
answer. No model provider or API key is needed.

First complete the [portable trust demo](PORTABLE_TRUST_DEMO.md), including the
pinned external checker build. Also clone SMC17/zag and build it with Zig
0.16.0. zag's development runtime is Linux; this example does not add macOS
runtime support.

From a directory containing both checkouts:

```sh
(cd zag && zig build)
export DEMO_LOGIC_REPO="$(cd logic-zig && pwd)"
export DEMO_ZAG_BIN="$(cd zag/zig-out/bin && pwd)"
mkdir recorded-proof-demo
cd recorded-proof-demo

"$DEMO_ZAG_BIN/zag" run -- /bin/sh -c \
  'cd "$DEMO_LOGIC_REPO" && exec ./zig-out/bin/logic-zig trust-report'
"$DEMO_ZAG_BIN/zagd" verify
"$DEMO_ZAG_BIN/zag" history trust-report
```

Use a fresh demonstration directory. The task runs in the logic-zig repository
so it can locate its checker builds and corpus fixtures. Its command and output
are recorded in the separate workspace. Inspect `.workspace/events.jsonl` and
use `zagd verify` to verify the referenced output objects as well as the log.

Measured on Ubuntu 24.04 ARM64 with Zig 0.16.0 on 11 November 2026:

- The repository-context task returned TRUST_OK: five verified DRAT checks,
  25 CaDiCaL comparisons with zero mismatches, and positive internal axes.
- An earlier attempt launched from the fresh workspace without that context
  returned TRUST_FAIL because ABC was unavailable there.
- zag preserved both commands, their outputs and their exit statuses.
- The resulting ten-event chain and two referenced output objects verified.

That earlier refusal is specific to the tested discovery context; a machine
with checkers on PATH may discover different tools. Both attempts remain in the
measured record. An intact record is evidence of what ran, not a substitute for
the checker's evidence. This example does not exercise model tool approval,
policy refusal, crash recovery or multi-client behavior. Hosted CI remains
subject to the account billing restriction.

Source revisions exercised: logic-zig repair head
`1fb677db132ffa6835b0cd9fa9e8dfd271d7a4ec` (merged as `9ecee09`), and zag
`13d2d9fbb0636506b56bd892ef6cd9ba6e163c7b`.
