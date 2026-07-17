//! k-Liveness / fair multi-justice: infinite-trace proofs.
//!
//! HWMCC justice is **violated** by an infinite path on which each justice
//! (and each fairness constraint) is true infinitely often.
//!
//! ## Single signal
//! Thermometer: t_i means “≥ i+1 hits”. Bad ≡ t_k. Safety ⇒ only finitely often.
//!
//! ## Multi justice + fairness (complete reduction)
//! Round-robin phase over the concatenated signal list S = justice ∥ fairness:
//! wait for S[p], then p ← (p+1) mod |S|. Each full wrap increments a round
//! thermometer. If rounds ≤ k is inductive/safe, some S[i] is only finite often
//! on every path — so no fair multi-justice infinite path exists.
//! This is complete relative to the underlying safety engine (kind/PDR).

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
        var pr = try pdr.check(allocator, &work, bad, pdr_frames);
        defer pr.deinit(allocator);
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

/// Attach round-robin phase + thermometer over `signals` (justice∥fairness).
/// Returns bad = “completed more than k full cycles”.
pub fn attachFairRoundRobin(
    nl: *Netlist,
    signals: []const NetId,
    k: u32,
) !NetId {
    std.debug.assert(signals.len > 0);
    const n: u32 = @intCast(signals.len);

    // One-hot phase latches
    var phase = try nl.allocator.alloc(NetId, n);
    defer nl.allocator.free(phase);
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        phase[i] = try nl.allocNet();
    }
    // next_phase[j]
    var next = try nl.allocator.alloc(NetId, n);
    defer nl.allocator.free(next);
    i = 0;
    while (i < n) : (i += 1) {
        // next_i = (phase_i ∧ ¬sig_i) ∨ (phase_prev ∧ sig_prev)
        // prev = (i + n - 1) % n
        const prev: u32 = if (i == 0) n - 1 else i - 1;
        const stay = try nl.allocNet();
        const nsig = try nl.allocNet();
        try nl.addGate(.not, &.{signals[i]}, nsig);
        try nl.addGate(.and_, &.{ phase[i], nsig }, stay);
        const adv = try nl.allocNet();
        try nl.addGate(.and_, &.{ phase[prev], signals[prev] }, adv);
        next[i] = try nl.allocNet();
        try nl.addGate(.or_, &.{ stay, adv }, next[i]);
        // init: phase0=1, others=0
        try nl.addLatch(next[i], phase[i], i == 0);
    }

    // round_inc = phase_{n-1} ∧ sig_{n-1}
    const round_inc = try nl.allocNet();
    try nl.addGate(.and_, &.{ phase[n - 1], signals[n - 1] }, round_inc);
    return try attachThermometer(nl, round_inc, k);
}

/// Prove multi-fair justice cannot all hold i.o. (complete k-liveness).
pub fn proveFairMulti(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    signals: []const NetId,
    max_k: u32,
    pdr_frames: u32,
) !KLiveResult {
    if (signals.len == 0) return .{ .status = .proven_infinite, .k = 0 };
    if (signals.len == 1) return proveFiniteHits(allocator, nl, signals[0], max_k, pdr_frames);

    var k: u32 = 0;
    var total_conf: u64 = 0;
    while (k <= max_k) : (k += 1) {
        var work = try cloneNetlist(allocator, nl);
        defer work.deinit();
        const bad = try attachFairRoundRobin(&work, signals, k);

        const kr = try kinduction.search(allocator, &work, bad, @max(k + 3, 4));
        defer if (kr.base.trace) |t| allocator.free(t);
        total_conf += kr.conflicts;
        if (kr.status == .proven) {
            return .{ .status = .proven_infinite, .k = k, .conflicts = total_conf, .pdr_frames = kr.k };
        }

        var pr = try pdr.check(allocator, &work, bad, pdr_frames);
        defer pr.deinit(allocator);
        total_conf += pr.conflicts;
        if (pr.status == .proven) {
            return .{ .status = .proven_infinite, .k = k, .conflicts = total_conf, .pdr_frames = pr.frames };
        }
    }
    return .{ .status = .unknown, .k = max_k, .conflicts = total_conf };
}

/// Full justice check: lasso witness first, then complete fair k-liveness.
pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    justices: []const NetId,
    max_k: u32,
    pdr_frames: u32,
    lasso_bound: u32,
) !KLiveResult {
    if (justices.len == 0) {
        return .{ .status = .proven_infinite, .k = 0 };
    }

    // Strong CEX: lasso fair path (justice + fairness on loop)
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

    // Complete multi: round-robin over justice ∥ fairness
    const fair = nl.fairness.items;
    if (justices.len == 1 and fair.len == 0) {
        return proveFiniteHits(allocator, nl, justices[0], max_k, pdr_frames);
    }
    const signals = try std.mem.concat(allocator, NetId, &.{ justices, fair });
    defer allocator.free(signals);
    return proveFairMulti(allocator, nl, signals, max_k, pdr_frames);
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

test "fair multi: one stuck-0 proves complete" {
    // Two justice: q0 stuck 0, q1 toggles. Round-robin cannot complete infinitely.
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    try nl.addConst(d0, false);
    try nl.addGate(.not, &.{q1}, d1);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    const r = try check(std.testing.allocator, &nl, &.{ q0, q1 }, 4, 16, 0);
    try std.testing.expect(r.status == .proven_infinite);
}

test "fair multi: both toggle not false-proven" {
    // Both latches toggle (xor chain) — may have fair path; must not proven_infinite at small k without lasso.
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
    // Counter visits all states; both bits true i.o. on the cycle — must not false-prove.
    const r = try check(std.testing.allocator, &nl, &.{ q0, q1 }, 2, 10, 6);
    try std.testing.expect(r.status != .proven_infinite);
}
