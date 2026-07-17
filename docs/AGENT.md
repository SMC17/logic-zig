# Agent-native formal (logic-agent)

## Why this flagship

LLM agents and tool runtimes issue **many small SAT queries** with shared structure.
Spawning CaDiCaL per call loses to a **warm multishot engine**.

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
