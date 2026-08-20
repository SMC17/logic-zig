# logic-zig dependency graph

Honest upstream / downstream map for `SMC17/logic-zig`.
Does not invent external adoption or stars.

## Upstream

| Dependency | Kind | Notes |
|------------|------|-------|
| **Zig 0.16.x** | Toolchain | Required. Tree targets 0.16 APIs (`ArrayList = .empty`, `std.process.Init`, …). |
| **CaDiCaL** (optional) | External binary | Differential SAT oracle / scoreboard only. Not linked. Discover via PATH or `LOGIC_ZIG_EXTERNAL_SOLVER`. |
| **Kissat / Z3 / ABC / Vampire / drat-trim** (optional) | External binaries | Discovered by `bridge/giants`; never hard deps. |
| **AIGER / Yosys JSON / DIMACS / BTOR2** | Formats | Interchange formats, not package dependencies. |
| **Lean / Coq** (optional peers) | External | Documented as giants; no link-time dependency on `main`. |

### `build.zig.zon`

Path / git dependencies, if any, must be listed here when introduced.
As of v0.21 the library is self-contained Zig with **no required package deps**
beyond the Zig standard library.

## Internal graph (in-tree spin-offs)

```
logic (src/root.zig)
├── logic-zig          # umbrella CLI
├── logic-agent        # multishot / agent profile
├── logic-sat          # competition SAT profile
├── logic-hwmcc        # sequential MC / AIGER profile
├── logic-cert         # certificates / klive
├── logic-smt          # BV-SMT facade
├── logic-ctl          # bounded CTL
└── ipasir-consumer    # IPASIR C ABI smoke
```

All spin-offs consume the single `logic` module. No circular deps.

## Downstream

| Consumer | Status |
|----------|--------|
| In-tree spin-offs listed above | Active |
| External agent / HWMCC tooling | None declared — add here when real |
| Package consumers via `build.zig.zon` | None declared yet |

Downstream is intentionally empty of external claims until evidence exists.

## License compatibility

- logic-zig: **Apache-2.0**
- Optional external solvers retain their own licenses (CaDiCaL MIT, etc.) and
  are invoked as subprocesses, not redistributed.
