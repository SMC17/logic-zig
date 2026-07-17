//! Bounded CTL model checking via SAT unrolling (explicit-path semantics).
//!
//! Supported (bounded):
//! - EF φ  — exists path of length ≤ k reaching φ
//! - EG φ  — exists path of length k where φ holds at every frame
//! - AF φ  — all paths hit φ within k (UNSAT of “avoid φ for k steps”)
//! - AG φ  — all paths stay in φ for k steps (UNSAT of EF ¬φ)
//! - Fair EG: EG φ under justice signals (lasso-style fair path) — delegates justice
//!
//! Not a full symbolic CTL model checker (no BDDs / complete fair-CTL fixpoints).

const std = @import("std");
const netlist_mod = @import("../circuit/netlist.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");
const blast = @import("../circuit/blast.zig");
const justice = @import("../circuit/justice.zig");

const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const CtlOp = enum { ef, eg, af, ag, fair_eg };

pub const CtlStatus = enum { holds, fails, unknown };

pub const CtlResult = struct {
    status: CtlStatus,
    op: CtlOp,
    bound: u32,
    conflicts: u64 = 0,
};

fn unroll(allocator: std.mem.Allocator, nl: *const Netlist, bound: u32) !struct { cnf: Cnf, nn: u32, frames: u32 } {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();
    const nn = nl.num_nets;
    const frames = bound + 1;
    cnf.ensureVars(nn * frames + 8);
    var t: u32 = 0;
    while (t < frames) : (t += 1) try blast.blastFrame(&cnf, nl, t);
    for (nl.latches.items) |lat| {
        if (lat.init) |iv| {
            const q = Lit.positive(Var.fromIndex(lat.q.index()));
            if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
        }
    }
    for (nl.constraints.items) |c| {
        t = 0;
        while (t < frames) : (t += 1) {
            try cnf.addClause(&.{Lit.positive(Var.fromIndex(t * nn + c.index()))});
        }
    }
    t = 0;
    while (t < bound) : (t += 1) {
        for (nl.latches.items) |lat| {
            const qn = Lit.positive(Var.fromIndex((t + 1) * nn + lat.q.index()));
            const d = Lit.positive(Var.fromIndex(t * nn + lat.d.index()));
            try cnf.addClause(&.{ qn.not(), d });
            try cnf.addClause(&.{ d.not(), qn });
        }
    }
    return .{ .cnf = cnf, .nn = nn, .frames = frames };
}

/// EF φ: some frame has φ.
pub fn checkEf(allocator: std.mem.Allocator, nl: *const Netlist, prop: NetId, bound: u32) !CtlResult {
    var u = try unroll(allocator, nl, bound);
    defer u.cnf.deinit();
    var cl: std.ArrayList(Lit) = .empty;
    defer cl.deinit(allocator);
    var t: u32 = 0;
    while (t < u.frames) : (t += 1) {
        try cl.append(allocator, Lit.positive(Var.fromIndex(t * u.nn + prop.index())));
    }
    try u.cnf.addClause(cl.items);
    const r = try solver_mod.solveCnf(allocator, &u.cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return switch (r.status) {
        .sat => .{ .status = .holds, .op = .ef, .bound = bound, .conflicts = r.conflicts },
        .unsat => .{ .status = .fails, .op = .ef, .bound = bound, .conflicts = r.conflicts },
        .unknown => .{ .status = .unknown, .op = .ef, .bound = bound, .conflicts = r.conflicts },
    };
}

/// EG φ (bounded): φ at every frame 0..bound (path existence).
pub fn checkEg(allocator: std.mem.Allocator, nl: *const Netlist, prop: NetId, bound: u32) !CtlResult {
    var u = try unroll(allocator, nl, bound);
    defer u.cnf.deinit();
    var t: u32 = 0;
    while (t < u.frames) : (t += 1) {
        try u.cnf.addClause(&.{Lit.positive(Var.fromIndex(t * u.nn + prop.index()))});
    }
    const r = try solver_mod.solveCnf(allocator, &u.cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return switch (r.status) {
        .sat => .{ .status = .holds, .op = .eg, .bound = bound, .conflicts = r.conflicts },
        .unsat => .{ .status = .fails, .op = .eg, .bound = bound, .conflicts = r.conflicts },
        .unknown => .{ .status = .unknown, .op = .eg, .bound = bound, .conflicts = r.conflicts },
    };
}

/// AG φ ≡ ¬EF ¬φ (bounded).
pub fn checkAg(allocator: std.mem.Allocator, nl: *const Netlist, prop: NetId, bound: u32) !CtlResult {
    // Build temp net for ¬prop? Use force prop false at some frame via EF of not.
    // Without not-net: EF(¬φ) = OR of ¬prop[t]
    var u = try unroll(allocator, nl, bound);
    defer u.cnf.deinit();
    var cl: std.ArrayList(Lit) = .empty;
    defer cl.deinit(allocator);
    var t: u32 = 0;
    while (t < u.frames) : (t += 1) {
        try cl.append(allocator, Lit.negative(Var.fromIndex(t * u.nn + prop.index())));
    }
    try u.cnf.addClause(cl.items);
    const r = try solver_mod.solveCnf(allocator, &u.cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    // If EF¬φ SAT → AG fails; UNSAT → AG holds within bound
    return switch (r.status) {
        .unsat => .{ .status = .holds, .op = .ag, .bound = bound, .conflicts = r.conflicts },
        .sat => .{ .status = .fails, .op = .ag, .bound = bound, .conflicts = r.conflicts },
        .unknown => .{ .status = .unknown, .op = .ag, .bound = bound, .conflicts = r.conflicts },
    };
}

/// AF φ ≡ ¬EG ¬φ (bounded path semantics).
pub fn checkAf(allocator: std.mem.Allocator, nl: *const Netlist, prop: NetId, bound: u32) !CtlResult {
    var u = try unroll(allocator, nl, bound);
    defer u.cnf.deinit();
    var t: u32 = 0;
    while (t < u.frames) : (t += 1) {
        try u.cnf.addClause(&.{Lit.negative(Var.fromIndex(t * u.nn + prop.index()))});
    }
    const r = try solver_mod.solveCnf(allocator, &u.cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return switch (r.status) {
        .unsat => .{ .status = .holds, .op = .af, .bound = bound, .conflicts = r.conflicts },
        .sat => .{ .status = .fails, .op = .af, .bound = bound, .conflicts = r.conflicts },
        .unknown => .{ .status = .unknown, .op = .af, .bound = bound, .conflicts = r.conflicts },
    };
}

pub fn checkFairEg(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    bound: u32,
) !CtlResult {
    const r = try justice.checkLasso(allocator, nl, justices, nl.fairness.items, bound);
    defer if (r.trace) |t| allocator.free(t);
    return switch (r.status) {
        .witness => .{ .status = .holds, .op = .fair_eg, .bound = bound, .conflicts = r.conflicts },
        .no_witness_within_bound => .{ .status = .fails, .op = .fair_eg, .bound = bound, .conflicts = r.conflicts },
        .unknown => .{ .status = .unknown, .op = .fair_eg, .bound = bound, .conflicts = r.conflicts },
    };
}

pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    op: CtlOp,
    prop: NetId,
    bound: u32,
) !CtlResult {
    return switch (op) {
        .ef => checkEf(allocator, nl, prop, bound),
        .eg => checkEg(allocator, nl, prop, bound),
        .af => checkAf(allocator, nl, prop, bound),
        .ag => checkAg(allocator, nl, prop, bound),
        .fair_eg => checkFairEg(allocator, nl, &.{prop}, bound),
    };
}

test "ctl AG true on stuck0" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    const nq = try nl.allocNetNamed("nq");
    try nl.addConst(d, false);
    try nl.addGate(.not, &.{q}, nq);
    try nl.addLatch(d, q, false);
    // AG ¬q : q always 0
    const r = try checkAg(std.testing.allocator, &nl, nq, 4);
    try std.testing.expect(r.status == .holds);
}

test "ctl EF reaches toggle 1" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    const r0 = try checkEf(std.testing.allocator, &nl, q, 0);
    try std.testing.expect(r0.status == .fails);
    const r1 = try checkEf(std.testing.allocator, &nl, q, 1);
    try std.testing.expect(r1.status == .holds);
}
