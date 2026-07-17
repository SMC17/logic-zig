# Getting started

## Install Zig

logic-zig targets **Zig 0.16**. Install from [ziglang.org](https://ziglang.org/download/)
or your package manager / Nix flake, then confirm:

```sh
zig version   # expect 0.16.x
```

## Build and test

```sh
git clone https://github.com/SMC17/logic-zig.git
cd logic-zig
zig build test
zig build
./zig-out/bin/logic-zig doctor
```

`doctor` runs a short end-to-end smoke suite (prop, CDCL, AIGER, PDR, k-liveness,
write/read). Exit status 0 means the core stack is healthy on your machine.

## First commands

```sh
# Propositional SAT
./zig-out/bin/logic-zig sat 'a | !a'          # tautological shape → sat
./zig-out/bin/logic-zig sat 'a & !a'          # unsat
./zig-out/bin/logic-zig sat --file corpus/simple_unsat.cnf --proof

# Sequential demos
./zig-out/bin/logic-zig bmc-demo --bound 3
./zig-out/bin/logic-zig pdr-demo --frames 12
./zig-out/bin/logic-zig klive-demo --max-k 4  # infinite justice proof vs lasso CEX

# AIGER
./zig-out/bin/logic-zig aiger corpus/and2.aag
./zig-out/bin/logic-zig aiger-write corpus/and2.aag /tmp/out.aag
```

## Use as a library

Point a dependent `build.zig` at this package (git URL or path) and import the
`logic` module the same way this repository’s executable does:

```zig
const logic = @import("logic");
```

Public entry points live in `src/root.zig`.

## Next reading

- [ARCHITECTURE.md](ARCHITECTURE.md) — data flow
- [ENGINES.md](ENGINES.md) — contracts per engine
- [../STATUS.md](../STATUS.md) — what is unit-tested vs residual
