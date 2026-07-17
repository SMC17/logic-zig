# logic-zig status

**Version:** 0.12.0  
**Last green:** 2026-07-16 — `zig build test` · `zig build` · doctor · golden · spin-offs

Proof level: **`unit-tested`**. Optional **`benchmarked`** axes when CaDiCaL is present.

## Architecture

| Layer | Artifact |
|-------|----------|
| **Core library** | `logic` module (`src/root.zig`) |
| **Umbrella CLI** | `logic-zig` |
| **Flagship spin-offs** | `logic-agent` · `logic-sat` · `logic-hwmcc` · `logic-cert` · `logic-smt` · `logic-ctl` |
| **C ABI** | `libipasirlogic.so` |
| **CI** | `.github/workflows/ci.yml` |

See [docs/PRODUCTS.md](docs/PRODUCTS.md) for profile tradeoffs.

## Tier coverage

| Tier | Status |
|------|--------|
| **A** CI, golden suite, doctor, multishot agent path | shipped |
| **B** certificates (k-live + inductive verify), BTOR2 micro, PDR stack | shipped (honest residual: full clause dump from PDR) |
| **C** portfolio SAT, bounded CTL, BV-SMT, ABC discovery | shipped as micro/substrate — **not** Kissat/ABC/nuXmv parity |

## Residuals (explicit)

1. Industrial SAT Race hardness / full inprocessing portfolio — not claimed.
2. Full symbolic CTL/LTL (BDDs, automata) — bounded SAT-unroll only.
3. Full SMT-LIB / theory combination — BV bit-blast micro only.
4. ABC binary parity — optional interop discovery, no vendored ABC.
5. PDR inductive cert export still kind-backed for empty-I cases.

## Smoke

```sh
zig build test && zig build
./zig-out/bin/logic-zig doctor
./zig-out/bin/logic-hwmcc golden
./zig-out/bin/logic-agent profile
./zig-out/bin/logic-sat profile
./zig-out/bin/logic-cert klive-demo
./zig-out/bin/logic-smt demo-add
./zig-out/bin/logic-ctl demo
```
