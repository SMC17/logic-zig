//! k-Liveness: infinite-trace proofs for justice properties.
//!
//! AIGER/HWMCC justice is **violated** by an infinite path on which each
//! justice signal is true infinitely often. A **proof** is therefore a
//! demonstration that no such path exists.
//!
//! k-Liveness (Claessen / Sörensson style) reduces that claim to safety:
//!
//!   - Thermometer counter: bit `t_i` means “justice has held ≥ i+1 times”.
//!   - Bad ⇔ `t_k` (justice held ≥ k+1 times).
//!   - If safety PDR proves G(¬bad) for some k, then justice holds at most
//!     k times on **every** path from the initial states — hence only
//!     finitely often on every infinite path. That is an **infinite-trace
//!     proof** that the justice property is not violated.
//!
//! For multiple justice signals we prove FG(¬J_i) for each i (sound: if any
//! signal is only finitely often, no path has *all* signals infinitely often).
//! Completeness for multi-justice requires stronger fair-CTL methods.

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const pdr = @import("pdr.zig");
const bmc = @import("bmc.zig");
const kinduction = @import("kinduction.zig");
const justice = @import("justice.zig");

const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;

pub const KLiveStatus = enum {
    /// Infinite-trace proof: justice cannot hold i.o. on any path.
    proven_infinite,
    /// Found a finite witness / BMC CEX that justice is reachable enough times.
    violated,
    /// Bounded lasso witness of infinite fair path (stronger CEX).
    lasso_witness,
    /// Neither proof nor CEX within resource bounds.
    unknown,
};

pub const KLiveResult = struct {
    status: KLiveStatus,
    /// k for which safety was proven (when proven_infinite).
    k: u32 = 0,
    conflicts: u64 = 0,
    pdr_frames: u32 = 0,
    /// Which justice net was the bottleneck (multi).
    justice_index: u32 = 0,
};

/// Build thermometer k-liveness transform for a single justice net.
/// Returns the bad net (t_k) on the (mutated) netlist.
pub fn attachThermometer(
    nl: *Netlist,
    justice_net: NetId,
    k: u32,
) !NetId {
    // t_i: “seen justice at least i+1 times”
    // t_i' = t_i ∨ (justice ∧ (i==0 ? 1 : t_{i-1}))
    var prev: ?NetId = null;
    var bad: NetId = undefined;
    var i: u32 = 0;
    while (i <= k) : (i += 1) {
        const t = try nl.allocNet();
        const d = try nl.allocNet();
        if (i == 0) {
            // d = t ∨ justice
            try nl.addGate(.or_, &.{ t, justice_net }, d);
        } else {
            // d = t ∨ (justice ∧ prev)
            const both = try nl.allocNet();
            try nl.addGate(.and_, &.{ justice_net, prev.? }, both);
            try nl.addGate(.or_, &.{ t, both }, d);
        }
        try nl.addLatch(d, t, false);
        prev = t;
        if (i == k) bad = t;
    }
    return bad;
}

/// Prove (or refute) that a single justice signal can hold only finitely often.
pub fn proveFiniteHits(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justice_net: NetId,
    max_k: u32,
    pdr_frames: u32,
) !KLiveResult {
    var k: u32 = 0;
    var total_conf: u64 = 0;
    while (k <= max_k) : (k += 1) {
        var work = try cloneNetlist(allocator, nl);
        defer work.deinit();
        const bad = try attachThermometer(&work, justice_net, k);

        // k-induction is strong for thermometer counters (inductive invariants).
        const kr = try kinduction.search(allocator, &work, bad, @max(k + 2, 3));
        defer if (kr.base.trace) |t| allocator.free(t);
        total_conf += kr.conflicts;
        if (kr.status == .proven) {
            return .{
                .status = .proven_infinite,
                .k = k,
                .conflicts = total_conf,
                .pdr_frames = kr.k,
            };
        }

        // PDR as second engine
        const pr = try pdr.check(allocator, &work, bad, pdr_frames);
        defer if (pr.cex_latches) |c| allocator.free(c);
        total_conf += pr.conflicts;
        switch (pr.status) {
            .proven => return .{
                .status = .proven_infinite,
                .k = k,
                .conflicts = total_conf,
                .pdr_frames = pr.frames,
            },
            .violated => {
                // Counter can reach k+1 within the unrolled bound — raise k.
            },
            .unknown => {},
        }

        const br = try bmc.check(allocator, &work, bad, k + 2);
        defer if (br.trace) |t| allocator.free(t);
        total_conf += br.conflicts;
    }
    return .{ .status = .unknown, .k = max_k, .conflicts = total_conf };
}

/// Full justice check: lasso witness first, then k-liveness infinite proof.
pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    max_k: u32,
    pdr_frames: u32,
    lasso_bound: u32,
) !KLiveResult {
    if (justices.len == 0) {
        // Vacuous: no justice to satisfy infinitely often → no violation path.
        return .{ .status = .proven_infinite, .k = 0 };
    }

    // Strong CEX: lasso fair path
    if (lasso_bound > 0 and nl.latches.items.len > 0) {
        const lr = try justice.checkLasso(allocator, nl, justices, nl.fairness.items, lasso_bound);
        defer if (lr.trace) |t| allocator.free(t);
        if (lr.status == .witness) {
            return .{
                .status = .lasso_witness,
                .k = lasso_bound,
                .conflicts = lr.conflicts,
            };
        }
    }

    // Sound multi: prove each FG(¬J_i); any one infinite FG(¬J_i) proves no path has all J i.o.
    var total: u64 = 0;
    for (justices, 0..) |jnet, ji| {
        const r = try proveFiniteHits(allocator, nl, jnet, max_k, pdr_frames);
        total += r.conflicts;
        if (r.status == .proven_infinite) {
            return .{
                .status = .proven_infinite,
                .k = r.k,
                .conflicts = total,
                .pdr_frames = r.pdr_frames,
                .justice_index = @intCast(ji),
            };
        }
    }
    return .{ .status = .unknown, .k = max_k, .conflicts = total };
}

pub fn checkNetlist(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    max_k: u32,
    pdr_frames: u32,
    lasso_bound: u32,
) !KLiveResult {
    const j = if (nl.justice.items.len > 0) nl.justice.items else nl.outputs.items;
    return check(allocator, nl, j, max_k, pdr_frames, lasso_bound);
}

fn cloneNetlist(allocator: std.mem.Allocator, src: *const Netlist) !Netlist {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    // Allocate same number of nets with names
    var i: u32 = 0;
    while (i < src.num_nets) : (i += 1) {
        if (i < src.names.items.len) {
            if (src.names.items[i]) |name| {
                _ = try nl.allocNetNamed(name);
            } else _ = try nl.allocNet();
        } else _ = try nl.allocNet();
    }
    for (src.inputs.items) |n| try nl.addInput(n);
    for (src.outputs.items) |n| try nl.addOutput(n);
    for (src.gates.items) |g| {
        if (g.kind == .@"const") {
            try nl.addConst(g.output, g.const_val);
        } else {
            try nl.addGate(g.kind, g.inputs, g.output);
        }
    }
    for (src.latches.items) |lat| try nl.addLatch(lat.d, lat.q, lat.init);
    for (src.bad.items) |n| try nl.addBad(n);
    for (src.constraints.items) |n| try nl.addConstraint(n);
    for (src.justice.items) |n| try nl.addJustice(n);
    for (src.fairness.items) |n| try nl.addFairness(n);
    return nl;
}

test "k-liveness stuck zero proven at k=0" {
    // q stuck 0: justice=q never true → proven at k=0
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    const r = try proveFiniteHits(std.testing.allocator, &nl, q, 4, 16);
    try std.testing.expect(r.status == .proven_infinite);
    try std.testing.expect(r.k == 0);
}

test "k-liveness pulse once proven at k=1" {
    // q init 1, d=0 → justice true only at frame 0
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, true);
    const r = try proveFiniteHits(std.testing.allocator, &nl, q, 4, 20);
    try std.testing.expect(r.status == .proven_infinite);
    try std.testing.expect(r.k <= 1);
}

test "k-liveness toggle not false-proven" {
    // Toggle: justice true i.o. — must NOT return proven_infinite
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    const r = try check(std.testing.allocator, &nl, &.{q}, 3, 12, 4);
    try std.testing.expect(r.status != .proven_infinite);
    // Prefer lasso witness when bound allows
    try std.testing.expect(r.status == .lasso_witness or r.status == .unknown or r.status == .violated);
}
