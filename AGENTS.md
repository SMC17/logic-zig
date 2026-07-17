# Agent notes (logic-zig)

Public repository. Do **not** write private workstation paths, wallet data, or
internal harness state into this tree.

## Before claiming green

```sh
zig build test
zig build
./zig-out/bin/logic-zig doctor
```

## Proof discipline

- Prefer unit tests beside the module under change.
- Update `STATUS.md` residuals when closing or opening a gap.
- User-facing behavior → `CHANGELOG.md`.

## Zig 0.16

`ArrayList = .empty`, `std.process.Init`, no `std.fs.cwd()` writer patterns from older Zig.
