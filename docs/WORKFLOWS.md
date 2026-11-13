# Named reasoning workflows

`logic-agent run <workflow.json>` evaluates related questions over fixed clauses
using one multishot session. Input and output are JSON. The public Zig API exposes
the same runner through `logic.api.AgentWorkflow` in api/v1 1.1.0.

## Write an input

```json
{
  "schema_version": 1,
  "title": "Deployment approval",
  "variables": ["deploy", "approved"],
  "clauses": [["!deploy", "approved"]],
  "queries": [
    {"id": "blocked", "assumptions": ["deploy", "!approved"]},
    {"id": "consistent", "assumptions": ["deploy", "approved"]}
  ]
}
```

Each clause is an OR; the clause list is an AND. The clause above encodes
`NOT deploy OR approved`, or `deploy -> approved`. A name denotes a positive
literal; prefix `!` negates it. Each query adds its assumptions for that query
only. An empty clause makes the base inconsistent; an empty clause list is
unconstrained. An empty query list is refused rather than reported successful.

| Field | Contract |
|-------|----------|
| `schema_version` | Required integer 1 |
| `title` | Optional display text |
| `variables` | Required array of unique, nonempty names; names cannot start with `!` |
| `clauses` | Required array of literal arrays; every name must be declared |
| `queries` | Nonempty array of objects with a unique, nonempty `id` and optional `assumptions` |
| `max_conflicts` | Optional unsigned conflict budget, default 200000; not a wall-clock timeout |

Unknown fields, undeclared variables, duplicate IDs and duplicate assumptions
are errors. A name and its negation in one query are valid contradictory
assumptions. The CLI reads inputs up to 16 MiB; the library accepts the caller's
source slice and allocator.

## Read an answer

- `status: "sat"`: `model` contains named Boolean values. `model_verified`
  records checking against the original clauses and that query's assumptions.
  Unspecified variables receive values chosen by the solver.
- `status: "unsat"`: `core` lists conflicting assumptions. `core_verified`
  records a fresh solve of the original clauses with that subset. A separate
  recheck of every single-element deletion establishes `core_deletion_minimal`.
  If the base itself is inconsistent, the core can be empty.
- `status: "unknown"`: the budget did not establish an answer. Model and core
  remain null. No evidence is fabricated.

The rechecks use fresh solver instances. They are internal checks, not
independent-tool UNSAT certificates. Minimality and uniqueness require positive
SAT evidence for the relevant probes; an unknown probe cannot establish them.
The workflow reports minimality only when its own probes establish it.

The report includes `schema_version`, `kind`, `title`, `input_sha256`, `variables`,
`results`, `complete`, `status` and `scope`. The SHA-256 binds it to the exact
input bytes. It is not a signature. Status/exit behavior:

| Process status | JSON status | Meaning |
|----------------|-------------|---------|
| 0 | `WORKFLOW_OK` | Every query has a determinate answer with its model or core checked |
| 1 | `WORKFLOW_INCOMPLETE` | At least one query is unknown or its core recheck is inconclusive |
| 2 | `WORKFLOW_ERROR` | Invalid input, usage or an execution/validation error; `error_code` identifies it |

An UNSAT query can appear in a successful completed workflow. Application code
must inspect the answer for the specific proposed action, rather than treating
the process's success as authorization. A false minimality flag means that
stronger explanation claim was not established; read `core_verified` separately.

## Integrate from Zig

```zig
const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const source = @embedFile("deployment.json");
    var report = try logic.api.AgentWorkflow.run(init.gpa, source);
    defer report.deinit();

    var buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writer(init.io, &buffer);
    try report.writeJson(&stdout.interface);
    try stdout.interface.flush();
}
```

The report owns its parsed strings and output allocations until `deinit`;
the caller can release the original input after `run` returns. Use `Session`
directly when the application needs to add clauses interactively. The workflow
format holds its base fixed within a batch.

For the application side of the boundary, see `examples/deployment_gate.py`.
It pins every supplied fact, binds the report to the request hash, and returns
a refusal or unresolved decision when the expected evidence is absent.

## Replay saved safety certificates

`logic-cert verify-invariant <model.aag> <invariant.txt>` accepts a model with
one explicit bad property (or one output used as that property). It requires
the certificate's bad-net ID to match it, then checks:

1. `I AND bad` is UNSAT in states admitted by the model's constraints.
2. Every clause of `I` follows from the admitted initial states.
3. `I AND T AND NOT I'` is UNSAT across admitted transitions.

Every obligation needs UNSAT evidence. A SAT or unknown result refuses the
certificate. Initiation alone cannot certify safety. The parser accepts the
exported `kind/source/frames/clauses/bad` headers and zero-terminated signed
literal clauses, and refuses missing or trailing evidence. Source metadata
identifies how a candidate was obtained; it never bypasses checking.

For completed checks, JSON contains `verified`, `property_matches`, `status`,
`schema_version` and `scope`. Verified pairs exit 0; refused pairs exit 1.
Malformed input or usage also terminates nonzero and may have no JSON response.
This command covers one property per model; a whole multi-property model is
not certified by checking a certificate for only one of its properties.

The walkthrough emits canonical three-column ASCII latch records. The generic
reader retains historical compact fixtures; broader AIGER import/export
conformance remains a [named residual](../STATUS.md#interoperability-boundaries).
Use the saved paired models when reproducing this workflow's certificate check.

Worked commands, expected results and application boundaries:
[use cases](USE_CASES.md). Independent DRAT checking and fixture trust:
[trust contract](TRUST.md).
