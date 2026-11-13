# Agent-native formal (logic-agent)

Run named queries from JSON with `logic-agent run examples/workflows/deployment.json`.
It returns checked assignments or named conflict cores, and preserves unknown
results. See [real use cases](USE_CASES.md) and the [workflow contract](WORKFLOWS.md).

For a complete worked task, start with the
[deployment policy example](../examples/policy/README.md): explicit inputs,
an exported proof, an independent check and refusal after the input changes.

## Machine-readable trust evidence

`logic-zig trust-report --json` writes schema-versioned evidence to stdout and
exits 1 on refusal. Require process success, `schema_version == 1`,
`status == "TRUST_OK"`, and `passed == true`. This checks a finite fixture suite;
an application must still validate the particular input and proof before
authorizing an action. Exact counters and boundaries: [trust contract](TRUST.md).

## Why this flagship

LLM agents and tool runtimes can issue many related SAT queries. A session keeps
one engine and its learned clauses across them. Measure the actual workload;
the bundled warm/cold comparison does not establish a universal speedup.

## API (Zig)

```zig
var s = logic.agent_session.Session.init(gpa);
defer s.deinit();
s.ensureVars(32);
try s.addClause(&.{ lit_a, lit_b });
var r = try s.query(&.{ lit_a.not() });
defer r.deinit(gpa);
// r.status, r.core, r.core_unique, r.model
```

Dimacs path: `addDimacsClause`, `queryDimacs`.

## IPASIR C / Zig

```zig
var s = logic.IpasirSolver.init(gpa);
try s.add(1); try s.add(2); try s.add(0);
_ = try s.solve();
_ = s.val(1);
try s.assume(-1);
_ = try s.solve(); // unsat + failed()
```

Shared library: `libipasirlogic.so` + `include/ipasir.h`.

## Benchmarks

```sh
./zig-out/bin/logic-agent stress --queries 1000 --vars 12
./zig-out/bin/logic-agent warm-cold --queries 200 --vars 10
./zig-out/bin/logic-agent session-demo
./zig-out/bin/logic-agent multishot --queries 80 --vars 16
```

Warm session keeps learned clauses; cold rebuilds every query. Expect lower total
conflicts on warm for incremental workloads (instance-dependent).

## Proofs

`session.enable_proof = true` logs RUP on queries (slower). Use for cert paths, not
default agent throughput.
