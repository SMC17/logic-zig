# Product matrix — core + flagship spin-offs

**logic-zig** is a **shared core library** (`logic` module) with **flagship CLIs**
that each pin a named optimization **profile** and a coherent tradeoff surface.

```
                    ┌─────────────────────┐
                    │   logic (core lib)  │
                    │ SAT · MC · cert · … │
                    └──────────┬──────────┘
           ┌───────────┬───────┼───────┬───────────┬──────────┐
           ▼           ▼       ▼       ▼           ▼          ▼
      logic-agent  logic-sat logic-hwmcc logic-cert logic-smt logic-ctl
      multishot    portfolio  AIGER MC    proofs     BV blast  bounded CTL
```

## Profiles (`src/profile/profiles.zig`)

| Profile | Flagship | Optimize for | Sacrifice |
|---------|----------|--------------|-----------|
| `core` | `logic-zig` | Balanced API | Peak domain performance |
| `agent` | `logic-agent` | Incremental QPS, assumptions | Heavy inprocessing |
| `sat-race` | `logic-sat` | Throughput / portfolio | Proofs, industrial hardness claims |
| `hwmcc` | `logic-hwmcc` | Frames / liveness budgets | SAT microbenchmarks |
| `cert` | `logic-cert` | RUP + k-liveness certificates | Speed |
| `smt` | `logic-smt` | BV bit-blast completeness | Word-level decision procedures |
| `ctl` | `logic-ctl` | Bounded EF/EG/AF/AG/fair-EG | Full symbolic CTL |

## Tier coverage (honest)

| Tier | Shipped in core / spin-offs | Ceiling note |
|------|----------------------------|--------------|
| **A** CI, golden, doctor, differential hooks | ✓ CI workflow, `golden`, ABC probe | Need ABC installed for baseline |
| **B** certificates, PDR stack, BTOR2/Yosys | ✓ cert module, btor2 micro, PDR | Invariant export still kind-backed |
| **C** portfolio, CTL, BV-SMT, ABC interop | ✓ modules + spin-offs | Not Kissat/ABC/nuXmv parity |
| **Industrial program** | `api/v1` · preprocess · SMT facade · FOL resolution | See [INDUSTRIAL.md](INDUSTRIAL.md) |

## Stable API

Prefer `@import("logic").api` (`src/api/v1.zig`) for long-lived integrations:

```zig
const api = @import("logic").api;
// api.version_string, api.Capability.current()
// api.satDimacs(allocator, src, .{ .preprocess = true })
// api.mcAiger(allocator, aig_src, .{ .cert = true })
```

## Build

```sh
zig build test
zig build                 # umbrella + all spin-offs + libipasirlogic.so
zig build spinoffs        # alias → install
```

Binaries under `zig-out/bin/`:

- `logic-zig` — umbrella
- `logic-agent`, `logic-sat`, `logic-hwmcc`, `logic-cert`, `logic-smt`, `logic-ctl`
