//! Simple k-induction for safety properties on sequential netlists.
//!
//! Property: G(¬bad)  (bad never true).
//!
//! Base (BMC):    I ∧ T^k ∧ (bad₀ ∨ … ∨ bad_k)  UNSAT
//! Step:          (¬bad₀ ∧ … ∧ ¬bad_{k-1}) ∧ T^k ∧ bad_k  UNSAT  (no init)
//!
//! If base holds for all j≤k and step holds at k, then ¬bad is invariant for all time
//! (Sheeran–Singh–Stålmarck style simple k-induction).

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const bmc_mod = @import("bmc.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const KindStatus = enum {
    /// Counterexample within base bound.
    violated,
    /// Base safe but step not inductive at this k.
    base_only,
    /// Base + inductive step both hold → property proven.
    proven,
    unknown,
};

pub const KindResult = struct {
    status: KindStatus,
    k: u32,
    base: bmc_mod.BmcResult,
    step_unsat: bool = false,
    conflicts: u64 = 0,
};

fn frameVar(num_nets: u32, frame: u32, net: NetId) Var {
    return Var.fromIndex(frame * num_nets + net.index());
}

const blast = @import("blast.zig");

fn blastFrame(cnf: *Cnf, nl: *const Netlist, frame: u32) !void {
    try blast.blastFrame(cnf, nl, frame);
}

/// Inductive step at k: path of length k with ¬bad on 0..k-1 and bad at k, no init.
fn checkStep(allocator: std.mem.Allocator, nl: *const Netlist, bad: NetId, k: u32) !struct { unsat: bool, conflicts: u64 } {
    if (k == 0) {
        // 0-induction: bad alone without init — usually SAT; treat as not inductive.
        return .{ .unsat = false, .conflicts = 0 };
    }

    var cnf = Cnf.init(allocator);
    defer cnf.deinit();
    const nn = nl.num_nets;
    const frames = k + 1;
    cnf.ensureVars(nn * frames);

    var t: u32 = 0;
    while (t < frames) : (t += 1) {
        try blastFrame(&cnf, nl, t);
        for (nl.constraints.items) |cnet| {
            try cnf.addClause(&.{Lit.positive(frameVar(nn, t, cnet))});
        }
    }

    t = 0;
    while (t < k) : (t += 1) {
        for (nl.latches.items) |lat| {
            const qn = Lit.positive(frameVar(nn, t + 1, lat.q));
            const d = Lit.positive(frameVar(nn, t, lat.d));
            try cnf.addClause(&.{ qn.not(), d });
            try cnf.addClause(&.{ d.not(), qn });
        }
    }

    // ¬bad on 0..k-1
    t = 0;
    while (t < k) : (t += 1) {
        try cnf.addClause(&.{Lit.negative(frameVar(nn, t, bad))});
    }
    // bad at k
    try cnf.addClause(&.{Lit.positive(frameVar(nn, k, bad))});

    const r = try solver_mod.solveCnf(allocator, &cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return .{ .unsat = r.status == .unsat, .conflicts = r.conflicts };
}

/// Run simple k-induction for G(¬bad) at a single k.
pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bad: NetId,
    k: u32,
) !KindResult {
    // Base: BMC must be safe for this k (and ideally all smaller — we check this k).
    var base = try bmc_mod.check(allocator, nl, bad, k);
    if (base.status == .violated) {
        return .{
            .status = .violated,
            .k = k,
            .base = base,
            .conflicts = base.conflicts,
        };
    }
    if (base.status == .unknown) {
        return .{ .status = .unknown, .k = k, .base = base, .conflicts = base.conflicts };
    }

    // Also require bases for all j < k? For simple k-induction completeness, yes.
    // Check j=0..k-1 BMC quickly.
    var j: u32 = 0;
    while (j < k) : (j += 1) {
        const bj = try bmc_mod.check(allocator, nl, bad, j);
        defer if (bj.trace) |tr| allocator.free(tr);
        if (bj.status == .violated) {
            // Transfer violation from smaller bound.
            if (base.trace) |tr| allocator.free(tr);
            base = try bmc_mod.check(allocator, nl, bad, j);
            return .{ .status = .violated, .k = j, .base = base, .conflicts = base.conflicts };
        }
    }

    const step = try checkStep(allocator, nl, bad, k);
    const conflicts = base.conflicts + step.conflicts;
    if (step.unsat) {
        return .{
            .status = .proven,
            .k = k,
            .base = base,
            .step_unsat = true,
            .conflicts = conflicts,
        };
    }
    return .{
        .status = .base_only,
        .k = k,
        .base = base,
        .step_unsat = false,
        .conflicts = conflicts,
    };
}

/// Search increasing k from 0..max_k for a proof or violation.
pub fn search(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bad: NetId,
    max_k: u32,
) !KindResult {
    var k: u32 = 0;
    while (k <= max_k) : (k += 1) {
        var r = try check(allocator, nl, bad, k);
        if (r.status == .violated or r.status == .proven or r.status == .unknown) {
            return r;
        }
        // base_only: free trace if any and continue
        if (r.base.trace) |tr| allocator.free(tr);
        r.base.trace = null;
    }
    // Last base_only at max_k
    return try check(allocator, nl, bad, max_k);
}

test "k-induction stuck-at-zero is proven" {
    // Latch stuck at 0: d=0, q init 0, bad=q → never bad. 0-induction? step at k=1.
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);

    const r = try search(std.testing.allocator, &nl, q, 3);
    defer if (r.base.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .proven);
}

test "k-induction counter not proven at small k without enough base" {
    // Counter will violate at k=3; search should find violated not proven.
    var nl = Netlist.init(std.testing.allocator);
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

    const r = try search(std.testing.allocator, &nl, bad, 5);
    defer if (r.base.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .violated);
}
