//! Library of sequential designs for stress, goldens, and cert tests.
//! Non-toy nets: counters, shift registers, stuck fields, fair products.

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;

/// n-bit binary counter; bad = all-1s (reaches at step 2^n - 1 from 0).
pub fn makeCounter(allocator: std.mem.Allocator, n: u32) !struct { nl: Netlist, bad: NetId } {
    std.debug.assert(n >= 1 and n <= 10);
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();

    const q = try allocator.alloc(NetId, n);
    defer allocator.free(q);
    const d = try allocator.alloc(NetId, n);
    defer allocator.free(d);
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        q[i] = try nl.allocNet();
        d[i] = try nl.allocNet();
    }
    // d0 = !q0
    try nl.addGate(.not, &.{q[0]}, d[0]);
    // di = qi xor (q0 & q1 & ... & q{i-1})  carry chain
    i = 1;
    while (i < n) : (i += 1) {
        var carry = q[0];
        var j: u32 = 1;
        while (j < i) : (j += 1) {
            const c2 = try nl.allocNet();
            try nl.addGate(.and_, &.{ carry, q[j] }, c2);
            carry = c2;
        }
        try nl.addGate(.xor, &.{ q[i], carry }, d[i]);
    }
    i = 0;
    while (i < n) : (i += 1) try nl.addLatch(d[i], q[i], false);

    // bad = AND all q
    var acc = q[0];
    i = 1;
    while (i < n) : (i += 1) {
        const y = try nl.allocNet();
        try nl.addGate(.and_, &.{ acc, q[i] }, y);
        acc = y;
    }
    try nl.addBad(acc);
    try nl.addOutput(acc);
    return .{ .nl = nl, .bad = acc };
}

/// Shift register of width n: d_i = q_{i-1}, d0 = free input; bad = q_{n-1}.
pub fn makeShift(allocator: std.mem.Allocator, n: u32) !struct { nl: Netlist, bad: NetId, input: NetId } {
    std.debug.assert(n >= 2 and n <= 16);
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const inp = try nl.allocNetNamed("in");
    try nl.addInput(inp);
    const q = try allocator.alloc(NetId, n);
    defer allocator.free(q);
    var i: u32 = 0;
    while (i < n) : (i += 1) q[i] = try nl.allocNet();
    try nl.addLatch(inp, q[0], false);
    i = 1;
    while (i < n) : (i += 1) try nl.addLatch(q[i - 1], q[i], false);
    try nl.addBad(q[n - 1]);
    try nl.addOutput(q[n - 1]);
    return .{ .nl = nl, .bad = q[n - 1], .input = inp };
}

/// k stuck-0 latches (safe under bad = OR of all q).
pub fn makeMultiStuck0(allocator: std.mem.Allocator, k: u32) !struct { nl: Netlist, bad: NetId } {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    var acc: ?NetId = null;
    var i: u32 = 0;
    while (i < k) : (i += 1) {
        const q = try nl.allocNet();
        const d = try nl.allocNet();
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        if (acc) |a| {
            const y = try nl.allocNet();
            try nl.addGate(.or_, &.{ a, q }, y);
            acc = y;
        } else acc = q;
    }
    const bad = acc.?;
    try nl.addBad(bad);
    return .{ .nl = nl, .bad = bad };
}

/// Fair product: n toggles as justice (all can be i.o.) — should not false-prove.
pub fn makeAllToggleJustice(allocator: std.mem.Allocator, n: u32) !Netlist {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        const q = try nl.allocNet();
        const d = try nl.allocNet();
        try nl.addGate(.not, &.{q}, d);
        try nl.addLatch(d, q, i % 2 == 1); // phase offset
        try nl.addJustice(q);
    }
    return nl;
}

/// One dead justice among n toggles — must prove finite.
pub fn makeOneDeadAmongToggles(allocator: std.mem.Allocator, n_live: u32) !Netlist {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const dead = try nl.allocNet();
    const dd = try nl.allocNet();
    try nl.addConst(dd, false);
    try nl.addLatch(dd, dead, false);
    try nl.addJustice(dead);
    var i: u32 = 0;
    while (i < n_live) : (i += 1) {
        const q = try nl.allocNet();
        const d = try nl.allocNet();
        try nl.addGate(.not, &.{q}, d);
        try nl.addLatch(d, q, false);
        try nl.addJustice(q);
    }
    return nl;
}

test "counter 3bit bmc" {
    const bmc = @import("bmc.zig");
    var d = try makeCounter(std.testing.allocator, 3);
    defer d.nl.deinit();
    // 3-bit reaches 111 at step 7
    const r6 = try bmc.check(std.testing.allocator, &d.nl, d.bad, 6);
    defer if (r6.trace) |t| std.testing.allocator.free(t);
    const r7 = try bmc.check(std.testing.allocator, &d.nl, d.bad, 7);
    defer if (r7.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r6.status == .safe_up_to_bound);
    try std.testing.expect(r7.status == .violated);
}

test "multi stuck0 pdr proven" {
    const pdr = @import("pdr.zig");
    var d = try makeMultiStuck0(std.testing.allocator, 4);
    defer d.nl.deinit();
    var r = try pdr.check(std.testing.allocator, &d.nl, d.bad, 16);
    defer r.deinit(std.testing.allocator);
    try std.testing.expect(r.status == .proven);
}

test "one dead among toggles klive" {
    const kliveness = @import("kliveness.zig");
    var nl = try makeOneDeadAmongToggles(std.testing.allocator, 3);
    defer nl.deinit();
    const r = try kliveness.checkNetlist(std.testing.allocator, &nl, 6, 16, 0);
    try std.testing.expect(r.status == .proven_infinite);
}

/// Mutex: two latches, never both 1 if constraint ~(q0&q1); bad = both 1 without constraint.
pub fn makeMutex(allocator: std.mem.Allocator, with_constraint: bool) !struct { nl: Netlist, bad: NetId } {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    try nl.addInput(a);
    try nl.addInput(b);
    // free next via inputs (buf)
    try nl.addGate(.buf, &.{a}, d0);
    try nl.addGate(.buf, &.{b}, d1);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    const both = try nl.allocNetNamed("both");
    try nl.addGate(.and_, &.{ q0, q1 }, both);
    try nl.addBad(both);
    if (with_constraint) {
        const nboth = try nl.allocNetNamed("nboth");
        try nl.addGate(.not, &.{both}, nboth);
        try nl.addConstraint(nboth);
    }
    return .{ .nl = nl, .bad = both };
}

test "mutex with constraint never bad in bmc" {
    const bmc = @import("bmc.zig");
    var d = try makeMutex(std.testing.allocator, true);
    defer d.nl.deinit();
    const r = try bmc.check(std.testing.allocator, &d.nl, d.bad, 6);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .safe_up_to_bound);
}

test "mutex without constraint can violate" {
    const bmc = @import("bmc.zig");
    var d = try makeMutex(std.testing.allocator, false);
    defer d.nl.deinit();
    const r = try bmc.check(std.testing.allocator, &d.nl, d.bad, 2);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .violated);
}

test "counter 5bit bound" {
    const bmc = @import("bmc.zig");
    var d = try makeCounter(std.testing.allocator, 5);
    defer d.nl.deinit();
    const r30 = try bmc.check(std.testing.allocator, &d.nl, d.bad, 30);
    defer if (r30.trace) |t| std.testing.allocator.free(t);
    const r31 = try bmc.check(std.testing.allocator, &d.nl, d.bad, 31);
    defer if (r31.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r30.status == .safe_up_to_bound);
    try std.testing.expect(r31.status == .violated);
}

/// One-hot ring: q0→q1→…→q0; bad = weight≠1 is not checked — bad = all zero (unreachable from one-hot init).
pub fn makeOneHotRing(allocator: std.mem.Allocator, n: u32) !struct { nl: Netlist, bad: NetId } {
    std.debug.assert(n >= 2 and n <= 8);
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q = try allocator.alloc(NetId, n);
    defer allocator.free(q);
    var i: u32 = 0;
    while (i < n) : (i += 1) q[i] = try nl.allocNet();
    // d_i = q_{i-1}
    i = 0;
    while (i < n) : (i += 1) {
        const prev = if (i == 0) q[n - 1] else q[i - 1];
        try nl.addLatch(prev, q[i], i == 0); // one-hot init: only q0=1
    }
    // bad = all zero (AND of ~qi)
    var acc: ?NetId = null;
    i = 0;
    while (i < n) : (i += 1) {
        const nq = try nl.allocNet();
        try nl.addGate(.not, &.{q[i]}, nq);
        if (acc) |a| {
            const y = try nl.allocNet();
            try nl.addGate(.and_, &.{ a, nq }, y);
            acc = y;
        } else acc = nq;
    }
    const bad = acc.?;
    try nl.addBad(bad);
    return .{ .nl = nl, .bad = bad };
}

test "one-hot ring safe under pdr" {
    const pdr = @import("pdr.zig");
    var d = try makeOneHotRing(std.testing.allocator, 4);
    defer d.nl.deinit();
    var r = try pdr.check(std.testing.allocator, &d.nl, d.bad, 20);
    defer r.deinit(std.testing.allocator);
    try std.testing.expect(r.status == .proven or r.status == .unknown);
    // Should not be violated — all-zero unreachable from one-hot
    try std.testing.expect(r.status != .violated);
}

test "multi stuck kind proven" {
    const kinduction = @import("kinduction.zig");
    var d = try makeMultiStuck0(std.testing.allocator, 3);
    defer d.nl.deinit();
    const r = try kinduction.search(std.testing.allocator, &d.nl, d.bad, 4);
    defer if (r.base.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .proven);
}

// counter 6bit BMC to bound 63 is intentionally not a unit test (too heavy in Debug).
// Exercise via designs-demo / golden at smaller widths.

/// Johnson (twisted ring) counter: d0 = ~q_{n-1}, d_i = q_{i-1}.
/// Bad = all-1s (reachable after enough steps from 0…0) — unsafe.
pub fn makeJohnson(allocator: std.mem.Allocator, n: u32) !struct { nl: Netlist, bad: NetId } {
    std.debug.assert(n >= 2 and n <= 12);
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q = try allocator.alloc(NetId, n);
    defer allocator.free(q);
    var i: u32 = 0;
    while (i < n) : (i += 1) q[i] = try nl.allocNet();
    const nq_last = try nl.allocNet();
    try nl.addGate(.not, &.{q[n - 1]}, nq_last);
    try nl.addLatch(nq_last, q[0], false);
    i = 1;
    while (i < n) : (i += 1) try nl.addLatch(q[i - 1], q[i], false);
    // bad = AND all q (all-1s)
    var acc = q[0];
    i = 1;
    while (i < n) : (i += 1) {
        const y = try nl.allocNet();
        try nl.addGate(.and_, &.{ acc, q[i] }, y);
        acc = y;
    }
    try nl.addBad(acc);
    return .{ .nl = nl, .bad = acc };
}

/// Dual-rail latch pair: q and nq with d_nq = ~d; bad = q ∧ nq (illegal coding).
/// From consistent init, illegal state is unreachable if next-state preserves dual-rail.
pub fn makeDualRailSafe(allocator: std.mem.Allocator) !struct { nl: Netlist, bad: NetId } {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const nq = try nl.allocNetNamed("nq");
    const inp = try nl.allocNetNamed("in");
    try nl.addInput(inp);
    const ninp = try nl.allocNetNamed("nin");
    try nl.addGate(.not, &.{inp}, ninp);
    // dual-rail init: q=0, nq=1
    try nl.addLatch(inp, q, false);
    try nl.addLatch(ninp, nq, true);
    const both = try nl.allocNetNamed("illegal");
    try nl.addGate(.and_, &.{ q, nq }, both);
    try nl.addBad(both);
    return .{ .nl = nl, .bad = both };
}

/// Parity latch: accumulate XOR of free input; bad = false (never) — always safe.
pub fn makeParityNeverBad(allocator: std.mem.Allocator) !struct { nl: Netlist, bad: NetId } {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q = try nl.allocNetNamed("par");
    const inp = try nl.allocNetNamed("bit");
    try nl.addInput(inp);
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.xor, &.{ q, inp }, d);
    try nl.addLatch(d, q, false);
    const bad = try nl.allocNetNamed("never");
    try nl.addConst(bad, false);
    try nl.addBad(bad);
    return .{ .nl = nl, .bad = bad };
}

test "johnson 3bit eventually violates" {
    const bmc = @import("bmc.zig");
    var d = try makeJohnson(std.testing.allocator, 3);
    defer d.nl.deinit();
    // Johnson of width 3 visits 6 states; all-1s is one of them
    const r = try bmc.check(std.testing.allocator, &d.nl, d.bad, 12);
    defer if (r.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .violated);
}

test "dual rail safe under pdr" {
    const pdr = @import("pdr.zig");
    var d = try makeDualRailSafe(std.testing.allocator);
    defer d.nl.deinit();
    var r = try pdr.check(std.testing.allocator, &d.nl, d.bad, 16);
    defer r.deinit(std.testing.allocator);
    try std.testing.expect(r.status != .violated);
}

test "parity never-bad proven kind" {
    const kinduction = @import("kinduction.zig");
    var d = try makeParityNeverBad(std.testing.allocator);
    defer d.nl.deinit();
    const r = try kinduction.search(std.testing.allocator, &d.nl, d.bad, 3);
    defer if (r.base.trace) |t| std.testing.allocator.free(t);
    try std.testing.expect(r.status == .proven);
}
