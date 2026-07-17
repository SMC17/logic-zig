//! Bounded justice / fairness checking via unrolling + optional lasso.
//!
//! Justice J: path visits J at least once (bounded GF).
//! Fairness F: same as justice for bounded witnesses (must hold infinitely
//! often on a cycle — with lasso, each F is required somewhere on the loop).
//!
//! Lasso witness: exists 0 ≤ stem < loop_end ≤ bound with equal latch state
//! at stem and loop_end, and every justice/fairness hit on (stem, loop_end].

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

pub const JusticeStatus = enum {
    witness,
    no_witness_within_bound,
    unknown,
};

pub const JusticeResult = struct {
    status: JusticeStatus,
    bound: u32,
    conflicts: u64 = 0,
    trace: ?[]Value = null,
    /// When lasso: stem frame index (equal to loop_end latches).
    stem: ?u32 = null,
    loop_end: ?u32 = null,
};

const blast = @import("blast.zig");

fn blastFrame(cnf: *Cnf, nl: *const Netlist, frame: u32, nn: u32) !void {
    try blast.blastFrameNn(cnf, nl, frame, nn);
}

fn unrollBase(allocator: std.mem.Allocator, nl: *const Netlist, bound: u32) !struct { cnf: Cnf, nn: u32, frames: u32 } {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();
    const nn = nl.num_nets;
    const frames = bound + 1;
    cnf.ensureVars(nn * frames + 256);

    var t: u32 = 0;
    while (t < frames) : (t += 1) try blastFrame(&cnf, nl, t, nn);

    for (nl.latches.items) |lat| {
        if (lat.init) |iv| {
            const q = Lit.positive(Var.fromIndex(lat.q.index()));
            if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
        }
    }
    // Constraints at every frame (must stay true)
    for (nl.constraints.items) |cnet| {
        t = 0;
        while (t < frames) : (t += 1) {
            try cnf.addClause(&.{Lit.positive(Var.fromIndex(t * nn + cnet.index()))});
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

/// Finite path visiting each justice ≥ once (no cycle required).
pub fn checkPath(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    bound: u32,
) !JusticeResult {
    if (justices.len == 0) return .{ .status = .witness, .bound = bound };

    var base = try unrollBase(allocator, nl, bound);
    defer base.cnf.deinit();

    for (justices) |jnet| {
        var clause: std.ArrayList(Lit) = .empty;
        defer clause.deinit(allocator);
        var t: u32 = 0;
        while (t < base.frames) : (t += 1) {
            try clause.append(allocator, Lit.positive(Var.fromIndex(t * base.nn + jnet.index())));
        }
        try base.cnf.addClause(clause.items);
    }

    return finish(allocator, &base.cnf, base.nn, base.frames, bound, null, null);
}

/// Finite path (lasso=false) or lasso cycle witness (lasso=true).
pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    bound: u32,
    lasso: bool,
) !JusticeResult {
    if (lasso) return checkLasso(allocator, nl, justices, nl.fairness.items, bound);
    return checkPath(allocator, nl, justices, bound);
}

/// Lasso: choose stem s and end e > s with latch(s)==latch(e); justices/fairness
/// must hold somewhere in (s, e] (frames s+1 .. e).
pub fn checkLasso(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    fairness: []const NetId,
    bound: u32,
) !JusticeResult {
    if (bound == 0 or nl.latches.items.len == 0) {
        // Degenerate: no cycle possible — fall back to finite path.
        return checkPath(allocator, nl, justices, bound);
    }

    var base = try unrollBase(allocator, nl, bound);
    defer base.cnf.deinit();
    const nn = base.nn;
    const frames = base.frames;
    // Selector vars: sel[s][e] for 0 <= s < e <= bound  — too many.
    // Encode: pick stem and end with one-hot
    // stem_i, end_j binary one-hot
    var next_var: u32 = nn * frames;
    const stem_base = next_var;
    next_var += frames; // stem indicator per frame
    const end_base = next_var;
    next_var += frames;
    base.cnf.ensureVars(next_var + 64);

    // Exactly one stem, one end
    {
        var cl: std.ArrayList(Lit) = .empty;
        defer cl.deinit(allocator);
        var i: u32 = 0;
        while (i < frames) : (i += 1) try cl.append(allocator, Lit.positive(Var.fromIndex(stem_base + i)));
        try base.cnf.addClause(cl.items);
        i = 0;
        while (i < frames) : (i += 1) {
            var j = i + 1;
            while (j < frames) : (j += 1) {
                try base.cnf.addClause(&.{
                    Lit.negative(Var.fromIndex(stem_base + i)),
                    Lit.negative(Var.fromIndex(stem_base + j)),
                });
            }
        }
    }
    {
        var cl: std.ArrayList(Lit) = .empty;
        defer cl.deinit(allocator);
        var i: u32 = 0;
        while (i < frames) : (i += 1) try cl.append(allocator, Lit.positive(Var.fromIndex(end_base + i)));
        try base.cnf.addClause(cl.items);
        i = 0;
        while (i < frames) : (i += 1) {
            var j = i + 1;
            while (j < frames) : (j += 1) {
                try base.cnf.addClause(&.{
                    Lit.negative(Var.fromIndex(end_base + i)),
                    Lit.negative(Var.fromIndex(end_base + j)),
                });
            }
        }
    }
    // end > stem: for all s,e with e<=s forbid both
    var s: u32 = 0;
    while (s < frames) : (s += 1) {
        var e: u32 = 0;
        while (e <= s) : (e += 1) {
            try base.cnf.addClause(&.{
                Lit.negative(Var.fromIndex(stem_base + s)),
                Lit.negative(Var.fromIndex(end_base + e)),
            });
        }
    }
    // latch equal when stem=s and end=e
    s = 0;
    while (s < frames) : (s += 1) {
        var e = s + 1;
        while (e < frames) : (e += 1) {
            for (nl.latches.items) |lat| {
                const qs = Lit.positive(Var.fromIndex(s * nn + lat.q.index()));
                const qe = Lit.positive(Var.fromIndex(e * nn + lat.q.index()));
                // stem_s & end_e => qs <=> qe
                const ss = Lit.negative(Var.fromIndex(stem_base + s));
                const ee = Lit.negative(Var.fromIndex(end_base + e));
                try base.cnf.addClause(&.{ ss, ee, qs.not(), qe });
                try base.cnf.addClause(&.{ ss, ee, qe.not(), qs });
            }
        }
    }

    // Each justice: exists frame t with stem < t <= end and J at t
    // For each justice j: OR over s,e,t: stem_s & end_e & (s<t<=e) & J_t
    // Encoded: for each t, aux hit_t = J_t & (exists s<t end>=t with stem_s end_e)
    // Simpler: for each justice, OR over all frames t of (J_t AND in_loop_t)
    // in_loop_t <=> exists s < t, e >= t: stem_s & end_e
    const in_loop_base = next_var;
    next_var += frames;
    base.cnf.ensureVars(next_var + 8);
    var t: u32 = 0;
    while (t < frames) : (t += 1) {
        // in_loop[t] => OR of stem_s & end_e for s<t<=e
        // and reverse
        var pairs: std.ArrayList(Lit) = .empty;
        defer pairs.deinit(allocator);
        s = 0;
        while (s < t) : (s += 1) {
            var e = t;
            while (e < frames) : (e += 1) {
                // aux = stem_s & end_e
                const aux = next_var;
                next_var += 1;
                base.cnf.ensureVars(next_var);
                const al = Lit.positive(Var.fromIndex(aux));
                const ss = Lit.positive(Var.fromIndex(stem_base + s));
                const ee = Lit.positive(Var.fromIndex(end_base + e));
                try base.cnf.addClause(&.{ al.not(), ss });
                try base.cnf.addClause(&.{ al.not(), ee });
                try base.cnf.addClause(&.{ ss.not(), ee.not(), al });
                try pairs.append(allocator, al);
            }
        }
        const il = Lit.positive(Var.fromIndex(in_loop_base + t));
        if (pairs.items.len == 0) {
            try base.cnf.addClause(&.{il.not()});
        } else {
            var cl: std.ArrayList(Lit) = .empty;
            defer cl.deinit(allocator);
            try cl.append(allocator, il.not());
            for (pairs.items) |p| try cl.append(allocator, p);
            try base.cnf.addClause(cl.items);
            for (pairs.items) |p| try base.cnf.addClause(&.{ p.not(), il });
        }
    }

    const all_j = try std.mem.concat(allocator, NetId, &.{ justices, fairness });
    defer allocator.free(all_j);
    for (all_j) |jnet| {
        var cl: std.ArrayList(Lit) = .empty;
        defer cl.deinit(allocator);
        t = 0;
        while (t < frames) : (t += 1) {
            // hit = J_t & in_loop_t
            const aux = next_var;
            next_var += 1;
            base.cnf.ensureVars(next_var);
            const al = Lit.positive(Var.fromIndex(aux));
            const jt = Lit.positive(Var.fromIndex(t * nn + jnet.index()));
            const il = Lit.positive(Var.fromIndex(in_loop_base + t));
            try base.cnf.addClause(&.{ al.not(), jt });
            try base.cnf.addClause(&.{ al.not(), il });
            try base.cnf.addClause(&.{ jt.not(), il.not(), al });
            try cl.append(allocator, al);
        }
        if (cl.items.len > 0) try base.cnf.addClause(cl.items);
    }

    const r = try solver_mod.solveCnf(allocator, &base.cnf, .{});
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    switch (r.status) {
        .sat => {
            const full = r.model.?;
            defer allocator.free(full);
            const need = nn * frames;
            const trace = try allocator.alloc(Value, need);
            @memcpy(trace, full[0..need]);
            var stem_i: ?u32 = null;
            var end_i: ?u32 = null;
            t = 0;
            while (t < frames) : (t += 1) {
                if (full[stem_base + t] == .true_) stem_i = t;
                if (full[end_base + t] == .true_) end_i = t;
            }
            return .{
                .status = .witness,
                .bound = bound,
                .conflicts = r.conflicts,
                .trace = trace,
                .stem = stem_i,
                .loop_end = end_i,
            };
        },
        .unsat => return .{ .status = .no_witness_within_bound, .bound = bound, .conflicts = r.conflicts },
        .unknown => return .{ .status = .unknown, .bound = bound, .conflicts = r.conflicts },
    }
}

fn finish(allocator: std.mem.Allocator, cnf: *Cnf, nn: u32, frames: u32, bound: u32, stem: ?u32, loop_end: ?u32) !JusticeResult {
    const r = try solver_mod.solveCnf(allocator, cnf, .{});
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    switch (r.status) {
        .sat => {
            const full = r.model.?;
            defer allocator.free(full);
            const need = nn * frames;
            const trace = try allocator.alloc(Value, need);
            @memcpy(trace, full[0..need]);
            return .{
                .status = .witness,
                .bound = bound,
                .conflicts = r.conflicts,
                .trace = trace,
                .stem = stem,
                .loop_end = loop_end,
            };
        },
        .unsat => return .{ .status = .no_witness_within_bound, .bound = bound, .conflicts = r.conflicts },
        .unknown => return .{ .status = .unknown, .bound = bound, .conflicts = r.conflicts },
    }
}

pub fn checkEventuallyAlways(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    prop: NetId,
    bound: u32,
) !JusticeResult {
    return check(allocator, nl, &.{prop}, bound, false);
}

/// Use netlist.justice + fairness properties.
pub fn checkNetlist(allocator: std.mem.Allocator, nl: *const Netlist, bound: u32, lasso: bool) !JusticeResult {
    const j = if (nl.justice.items.len > 0) nl.justice.items else nl.outputs.items;
    if (lasso) return checkLasso(allocator, nl, j, nl.fairness.items, bound);
    return check(allocator, nl, j, bound, false);
}

test "justice hits output once" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);

    const r0 = try check(std.testing.allocator, &nl, &.{q}, 0, false);
    defer if (r0.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r0.status == .no_witness_within_bound);

    const r1 = try check(std.testing.allocator, &nl, &.{q}, 1, false);
    defer if (r1.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r1.status == .witness);
}

test "justice multi both required" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    try nl.addGate(.not, &.{q0}, d0);
    try nl.addGate(.xor, &.{ q1, q0 }, d1);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    const r = try check(std.testing.allocator, &nl, &.{ q0, q1 }, 3, false);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .witness);
}

test "lasso witness finds cycle" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    // Toggle: d=!q init 0 → 0,1,0,1...
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);
    const r = try checkLasso(std.testing.allocator, &nl, &.{q}, &.{}, 3);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .witness);
    try std.testing.expect(r.stem != null and r.loop_end != null);
    try std.testing.expect(r.loop_end.? > r.stem.?);
}
