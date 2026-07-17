//! Bounded model checking for sequential netlists with latches.
//!
//! Unrolls k frames:
//!   Init(q₀) ∧ ⋀_{t=0..k} Comb(x_t, q_t, d_t, …) ∧ ⋀_{t=0..k-1} (q_{t+1} ↔ d_t)
//!   ∧ (bad₀ ∨ … ∨ bad_k)
//!
//! SAT ⇒ counterexample path of length ≤ k; UNSAT ⇒ safe up to bound k.

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const BmcStatus = enum {
    /// Bad property reachable within bound.
    violated,
    /// No violation in 0..k frames (not a full safety proof).
    safe_up_to_bound,
    unknown,
};

pub const BmcResult = struct {
    status: BmcStatus,
    bound: u32,
    /// When violated: per-frame assignment of all nets (frames * num_nets), owned.
    trace: ?[]Value = null,
    conflicts: u64 = 0,
};

fn frameVar(num_nets: u32, frame: u32, net: NetId) Var {
    return Var.fromIndex(frame * num_nets + net.index());
}

fn frameLit(num_nets: u32, frame: u32, net: NetId, neg: bool) Lit {
    return Lit.make(frameVar(num_nets, frame, net), neg);
}

const blast = @import("blast.zig");

fn blastFrame(cnf: *Cnf, nl: *const Netlist, frame: u32) !void {
    try blast.blastFrame(cnf, nl, frame);
}

fn addConstraints(cnf: *Cnf, nl: *const Netlist, frames: u32) !void {
    const nn = nl.num_nets;
    for (nl.constraints.items) |cnet| {
        var t: u32 = 0;
        while (t < frames) : (t += 1) {
            try cnf.addClause(&.{Lit.positive(frameVar(nn, t, cnet))});
        }
    }
}

/// BMC: check whether `bad` net can be true in any frame 0..bound inclusive.
/// Invariant constraints (`nl.constraints`) are forced true at every frame.
pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bad: NetId,
    bound: u32,
) !BmcResult {
    return checkMulti(allocator, nl, &.{bad}, bound);
}

/// BMC over OR of several bad nets (HWMCC multi-property).
pub fn checkMulti(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bads: []const NetId,
    bound: u32,
) !BmcResult {
    if (bads.len == 0) return .{ .status = .safe_up_to_bound, .bound = bound };
    for (bads) |bad| {
        if (bad.index() >= nl.num_nets) return error.BadNet;
    }

    var cnf = Cnf.init(allocator);
    defer cnf.deinit();

    const nn = nl.num_nets;
    const frames = bound + 1;
    cnf.ensureVars(nn * frames + 4);

    var t: u32 = 0;
    while (t < frames) : (t += 1) {
        try blastFrame(&cnf, nl, t);
    }

    for (nl.latches.items) |lat| {
        if (lat.init) |iv| {
            const q0 = Lit.positive(frameVar(nn, 0, lat.q));
            if (iv) try cnf.addClause(&.{q0}) else try cnf.addClause(&.{q0.not()});
        }
    }
    try addConstraints(&cnf, nl, frames);

    t = 0;
    while (t < bound) : (t += 1) {
        for (nl.latches.items) |lat| {
            const qn = Lit.positive(frameVar(nn, t + 1, lat.q));
            const d = Lit.positive(frameVar(nn, t, lat.d));
            try cnf.addClause(&.{ qn.not(), d });
            try cnf.addClause(&.{ d.not(), qn });
        }
    }

    // Bad: some property true at some frame.
    const miter = Lit.positive(Var.fromIndex(nn * frames));
    cnf.ensureVars(nn * frames + 1);
    var clause: std.ArrayList(Lit) = .empty;
    defer clause.deinit(allocator);
    try clause.append(allocator, miter.not());
    t = 0;
    while (t < frames) : (t += 1) {
        for (bads) |bad| {
            const b = Lit.positive(frameVar(nn, t, bad));
            try cnf.addClause(&.{ b.not(), miter });
            try clause.append(allocator, b);
        }
    }
    try cnf.addClause(clause.items);
    try cnf.addClause(&.{miter});

    const r = try solver_mod.solveCnf(allocator, &cnf, .{});
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    switch (r.status) {
        .unsat => return .{
            .status = .safe_up_to_bound,
            .bound = bound,
            .conflicts = r.conflicts,
        },
        .unknown => return .{
            .status = .unknown,
            .bound = bound,
            .conflicts = r.conflicts,
        },
        .sat => {
            const full = r.model.?;
            defer allocator.free(full);
            const need = nn * frames;
            const trace = try allocator.alloc(Value, need);
            @memcpy(trace, full[0..need]);
            return .{
                .status = .violated,
                .bound = bound,
                .trace = trace,
                .conflicts = r.conflicts,
            };
        },
    }
}

/// Convenience: use `nl.badProps()`.
pub fn checkNetlist(allocator: std.mem.Allocator, nl: *const Netlist, bound: u32) !BmcResult {
    return checkMulti(allocator, nl, nl.badProps(), bound);
}

/// Value of net at frame in a BMC trace.
pub fn traceAt(trace: []const Value, num_nets: u32, frame: u32, net: NetId) Value {
    return trace[frame * num_nets + net.index()];
}

test "bmc counter reaches two" {
    // 2-bit counter: q1q0, increment each cycle. bad = (q1 & q0) = 3.
    // From 00, need 3 steps to reach 11. Bound 2 should be safe; bound 3 violated.
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();

    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    const bad = try nl.allocNetNamed("bad");

    // d0 = !q0
    try nl.addGate(.not, &.{q0}, d0);
    // d1 = q1 xor q0
    try nl.addGate(.xor, &.{ q1, q0 }, d1);
    // bad = q1 & q0
    try nl.addGate(.and_, &.{ q1, q0 }, bad);

    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);

    const r2 = try check(std.testing.allocator, &nl, bad, 2);
    defer if (r2.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r2.status == .safe_up_to_bound);

    const r3 = try check(std.testing.allocator, &nl, bad, 3);
    defer if (r3.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r3.status == .violated);
    try std.testing.expect(r3.trace != null);
    // At frame 3, bad should be true.
    try std.testing.expect(traceAt(r3.trace.?, nl.num_nets, 3, bad) == .true_);
}

test "bmc immediate bad" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, true);
    try nl.addLatch(d, q, true); // starts true
    // bad = q
    const r = try check(std.testing.allocator, &nl, q, 0);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .violated);
}

test "bmc constraint blocks path" {
    // q starts 0, d = !q → toggles. bad = q. Without constraint, bound 1 violated.
    // Constraint: force !q every frame → no path with bad.
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    const nq = try nl.allocNetNamed("nq");
    try nl.addGate(.not, &.{q}, d);
    try nl.addGate(.not, &.{q}, nq);
    try nl.addLatch(d, q, false);
    try nl.addConstraint(nq); // q must stay 0
    const r = try check(std.testing.allocator, &nl, q, 4);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .safe_up_to_bound);
}

test "bmc multi bad or" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, true);
    try nl.addLatch(d, q, true);
    const r = try checkMulti(std.testing.allocator, &nl, &.{q}, 0);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .violated);
}
