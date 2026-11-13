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

The native core CI runs on Linux and macOS. These checks do not install
independent solvers or certify their presence. No Windows runtime claim is made.

`doctor` runs a short end-to-end smoke suite (prop, CDCL, AIGER, PDR, k-liveness,
write/read). Exit status 0 means the core stack is healthy on your machine.

## Independent trust checks

`doctor` is a core smoke test. `trust-report` is stricter: it requires actual
DRAT verification, CaDiCaL differential runs, ABC discovery, and positive
results on each internal evidence axis. Missing or inconclusive checks block
`TRUST_OK`.

To build the pinned optional tools in a clean checkout (requires Git, Make,
and C/C++ compilers; downloads upstream source):

```sh
scripts/build-checkers.sh
./zig-out/bin/logic-zig trust-report
```

The setup script refuses to overwrite an existing checker directory. Existing
installations can be selected with `LOGIC_ZIG_EXTERNAL_SOLVER`,
`LOGIC_ZIG_DRAT_TRIM`, and `LOGIC_ZIG_ABC`, each set to an executable file path.
ABC discovery establishes availability; it is not independent verification of
every model-checking result.

SAT competition commands use exit status **10 for SAT** and **20 for UNSAT**.
The CI helper checks the specific expected status; it does not ignore errors:

```sh
scripts/expect-status.sh 20 ./zig-out/bin/logic-sat check-drat corpus/bench/sat/simple_unsat.cnf
```

`check-drat` requires a verified proof for its UNSAT success status. A missing,
failed, or unusable checker is an error, not successful proof verification.

## First commands

```sh
# Museum index + agent-trust surface (not a SAT-solver tour)
./zig-out/bin/logic-zig taxonomy
./zig-out/bin/logic-zig api-info
./zig-out/bin/logic-agent profile

# Propositional SAT (substrate)
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
