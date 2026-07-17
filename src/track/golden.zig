//! Golden corpus runner — Tier A vertical correctness.
//!
//! Manifest format (JSONL): each line
//!   {"path":"corpus/bench/sat/simple_unsat.cnf","kind":"cnf","expect":"unsat"}
//!   {"path":"corpus/and2.aag","kind":"aiger-safe","expect":"unknown"}  // or sat/unsat for prop
//!
//! expect for CNF: sat | unsat
//! expect for aiger-safe: safe | unsafe | unknown  (PDR+BMC with small frames)

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const aiger = @import("../bridge/aiger.zig");
const solver_mod = @import("../sat/solver.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");

pub const GoldenResult = struct {
    total: u32 = 0,
    passed: u32 = 0,
    failed: u32 = 0,
    skipped: u32 = 0,
};

fn expectEq(a: []const u8, b: []const u8) bool {
    return std.mem.eql(u8, a, b);
}

/// Built-in golden cases (no external manifest required).
pub fn runBuiltin(allocator: std.mem.Allocator) !GoldenResult {
    var res: GoldenResult = .{};

    // CNF unsat
    {
        res.total += 1;
        const src =
            \\p cnf 1 2
            \\1 0
            \\-1 0
        ;
        var cnf = try dimacs.parse(allocator, src);
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .unsat) res.passed += 1 else res.failed += 1;
    }
    // CNF sat
    {
        res.total += 1;
        const src =
            \\p cnf 2 1
            \\1 2 0
        ;
        var cnf = try dimacs.parse(allocator, src);
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .sat) res.passed += 1 else res.failed += 1;
    }
    // AIGER stuck-safe (const 0 latch, bad=q)
    {
        res.total += 1;
        var nl = @import("../circuit/netlist.zig").Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const pr = try pdr.check(allocator, &nl, q, 12);
        defer if (pr.cex_latches) |c| allocator.free(c);
        if (pr.status == .proven) res.passed += 1 else res.failed += 1;
    }
    // AIGER parse and2
    {
        res.total += 1;
        const src =
            \\aag 3 2 0 1 1
            \\2
            \\4
            \\6
            \\6 2 4
        ;
        var nl = try aiger.parse(allocator, src);
        defer nl.deinit();
        if (nl.inputs.items.len == 2 and nl.outputs.items.len == 1) res.passed += 1 else res.failed += 1;
    }
    // BMC counter violates
    {
        res.total += 1;
        var nl = @import("../circuit/netlist.zig").Netlist.init(allocator);
        defer nl.deinit();
        const q0 = try nl.allocNetNamed("q0");
        const q1 = try nl.allocNetNamed("q1");
        const d0 = try nl.allocNetNamed("d0");
        const d1 = try nl.allocNetNamed("d1");
        const bad = try nl.allocNetNamed("bad");
        try nl.addGate(.not, &.{q0}, d0);
        try nl.addGate(.xor, &.{ q1, q0 }, d1);
        try nl.addGate(.and_, &.{ q1, q0 }, bad);
        try nl.addLatch(d0, q0, false);
        try nl.addLatch(d1, q1, false);
        const br = try bmc.check(allocator, &nl, bad, 3);
        defer if (br.trace) |t| allocator.free(t);
        if (br.status == .violated) res.passed += 1 else res.failed += 1;
    }

    return res;
}

pub fn printResult(r: *const GoldenResult) void {
    std.debug.print("golden: {d}/{d} passed, {d} failed, {d} skipped\n", .{
        r.passed,
        r.total,
        r.failed,
        r.skipped,
    });
}

test "golden builtin all pass" {
    const r = try runBuiltin(std.testing.allocator);
    try std.testing.expect(r.failed == 0);
    try std.testing.expect(r.passed == r.total);
}
