//! Dung abstract argumentation frameworks.
//!
//! An AF is (Args, →) with → an attack relation. Shipped semantics:
//!
//!   grounded   — least fixpoint of the characteristic function F(S) =
//!                {a : S defends a} (polynomial, computed iteratively);
//!   admissible — conflict-free and self-defending;
//!   complete   — admissible and containing everything it defends;
//!   stable     — conflict-free and attacking every outside argument;
//!   preferred  — ⊆-maximal admissible.
//!
//! Extension enumeration is by subset enumeration (finite AFs, n ≤ 20 —
//! canonical fixtures, agent-scale argument graphs; no claim of ICCMA-scale
//! solving). Grounded needs no enumeration. Acceptance queries: credulous
//! (in some extension) and skeptical (in all extensions).

const std = @import("std");

pub const Af = struct {
    /// Number of arguments (ids 0..n-1).
    n: u32,
    /// (attacker, target) pairs.
    attacks: []const [2]u32,

    pub fn attacksArg(self: Af, a: u32, b: u32) bool {
        for (self.attacks) |at| {
            if (at[0] == a and at[1] == b) return true;
        }
        return false;
    }
};

pub const Semantics = enum { admissible, complete, grounded, stable, preferred };

fn conflictFree(af: Af, s: u32) bool {
    for (af.attacks) |at| {
        if ((s >> @intCast(at[0])) & 1 == 1 and (s >> @intCast(at[1])) & 1 == 1) return false;
    }
    return true;
}

/// S defends a: every attacker of a is attacked by S.
fn defends(af: Af, s: u32, a: u32) bool {
    for (af.attacks) |at| {
        if (at[1] != a) continue;
        const attacker = at[0];
        var countered = false;
        for (af.attacks) |at2| {
            if (at2[1] == attacker and (s >> @intCast(at2[0])) & 1 == 1) {
                countered = true;
                break;
            }
        }
        if (!countered) return false;
    }
    return true;
}

fn isAdmissible(af: Af, s: u32) bool {
    if (!conflictFree(af, s)) return false;
    for (0..af.n) |a| {
        if ((s >> @intCast(a)) & 1 == 1 and !defends(af, s, @intCast(a))) return false;
    }
    return true;
}

fn isComplete(af: Af, s: u32) bool {
    if (!isAdmissible(af, s)) return false;
    for (0..af.n) |a| {
        if ((s >> @intCast(a)) & 1 == 0 and defends(af, s, @intCast(a))) return false;
    }
    return true;
}

fn isStable(af: Af, s: u32) bool {
    if (!conflictFree(af, s)) return false;
    for (0..af.n) |a| {
        if ((s >> @intCast(a)) & 1 == 1) continue;
        var attacked = false;
        for (af.attacks) |at| {
            if (at[1] == a and (s >> @intCast(at[0])) & 1 == 1) {
                attacked = true;
                break;
            }
        }
        if (!attacked) return false;
    }
    return true;
}

/// Grounded extension as a bitmask — iterated characteristic function from ∅.
pub fn grounded(af: Af) u32 {
    std.debug.assert(af.n <= 20);
    var s: u32 = 0;
    while (true) {
        var next: u32 = 0;
        for (0..af.n) |a| {
            if (defends(af, s, @intCast(a))) next |= @as(u32, 1) << @intCast(a);
        }
        if (next == s) return s;
        s = next;
    }
}

pub const Extensions = struct {
    allocator: std.mem.Allocator,
    /// Extensions as bitmasks over argument ids.
    sets: std.ArrayList(u32) = .empty,

    pub fn deinit(self: *Extensions) void {
        self.sets.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn contains(self: *const Extensions, m: u32) bool {
        for (self.sets.items) |s| {
            if (s == m) return true;
        }
        return false;
    }
};

/// Enumerate all extensions under the given semantics.
pub fn extensions(allocator: std.mem.Allocator, af: Af, sem: Semantics) !Extensions {
    std.debug.assert(af.n <= 20);
    var out = Extensions{ .allocator = allocator };
    errdefer out.deinit();
    if (sem == .grounded) {
        try out.sets.append(allocator, grounded(af));
        return out;
    }
    const total: u32 = @as(u32, 1) << @intCast(af.n);
    var s: u32 = 0;
    while (s < total) : (s += 1) {
        const ok = switch (sem) {
            .admissible => isAdmissible(af, s),
            .complete => isComplete(af, s),
            .stable => isStable(af, s),
            .preferred => isAdmissible(af, s),
            .grounded => unreachable,
        };
        if (ok) try out.sets.append(allocator, s);
    }
    if (sem == .preferred) {
        // Keep ⊆-maximal admissible sets only.
        var keep: std.ArrayList(u32) = .empty;
        defer keep.deinit(allocator);
        for (out.sets.items) |a| {
            var maximal = true;
            for (out.sets.items) |b| {
                if (a != b and (a & b) == a) {
                    maximal = false;
                    break;
                }
            }
            if (maximal) try keep.append(allocator, a);
        }
        out.sets.clearRetainingCapacity();
        try out.sets.appendSlice(allocator, keep.items);
    }
    return out;
}

pub const Acceptance = enum { credulous, skeptical };

/// Is argument `a` accepted under the semantics/acceptance mode?
/// Skeptical over an empty extension set is false (engineering answer;
/// stable semantics can be extension-free).
pub fn accepted(
    allocator: std.mem.Allocator,
    af: Af,
    a: u32,
    sem: Semantics,
    mode: Acceptance,
) !bool {
    var exts = try extensions(allocator, af, sem);
    defer exts.deinit();
    if (exts.sets.items.len == 0) return false;
    const bit = @as(u32, 1) << @intCast(a);
    for (exts.sets.items) |s| {
        switch (mode) {
            .credulous => if (s & bit != 0) return true,
            .skeptical => if (s & bit == 0) return false,
        }
    }
    return mode == .skeptical;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn mask(args: []const u32) u32 {
    var m: u32 = 0;
    for (args) |a| m |= @as(u32, 1) << @intCast(a);
    return m;
}

test "af: chain a→b→c — reinstatement" {
    const af = Af{ .n = 3, .attacks = &.{ .{ 0, 1 }, .{ 1, 2 } } };
    try testing.expectEqual(mask(&.{ 0, 2 }), grounded(af));
    var st = try extensions(testing.allocator, af, .stable);
    defer st.deinit();
    try testing.expectEqual(@as(usize, 1), st.sets.items.len);
    try testing.expect(st.contains(mask(&.{ 0, 2 })));
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    try testing.expectEqual(@as(usize, 1), pr.sets.items.len);
    try testing.expect(pr.contains(mask(&.{ 0, 2 })));
}

test "af: mutual attack — two preferred/stable, empty grounded" {
    const af = Af{ .n = 2, .attacks = &.{ .{ 0, 1 }, .{ 1, 0 } } };
    try testing.expectEqual(@as(u32, 0), grounded(af));
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    try testing.expectEqual(@as(usize, 2), pr.sets.items.len);
    try testing.expect(pr.contains(mask(&.{0})) and pr.contains(mask(&.{1})));
    var st = try extensions(testing.allocator, af, .stable);
    defer st.deinit();
    try testing.expectEqual(@as(usize, 2), st.sets.items.len);
    // Credulous both; skeptical neither.
    try testing.expect(try accepted(testing.allocator, af, 0, .preferred, .credulous));
    try testing.expect(!try accepted(testing.allocator, af, 0, .preferred, .skeptical));
}

test "af: odd cycle — no stable extension, empty preferred" {
    const af = Af{ .n = 3, .attacks = &.{ .{ 0, 1 }, .{ 1, 2 }, .{ 2, 0 } } };
    try testing.expectEqual(@as(u32, 0), grounded(af));
    var st = try extensions(testing.allocator, af, .stable);
    defer st.deinit();
    try testing.expectEqual(@as(usize, 0), st.sets.items.len);
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    try testing.expectEqual(@as(usize, 1), pr.sets.items.len);
    try testing.expectEqual(@as(u32, 0), pr.sets.items[0]);
}

test "af: even cycle — alternating preferred = stable" {
    const af = Af{ .n = 4, .attacks = &.{ .{ 0, 1 }, .{ 1, 2 }, .{ 2, 3 }, .{ 3, 0 } } };
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    try testing.expectEqual(@as(usize, 2), pr.sets.items.len);
    try testing.expect(pr.contains(mask(&.{ 0, 2 })) and pr.contains(mask(&.{ 1, 3 })));
    var st = try extensions(testing.allocator, af, .stable);
    defer st.deinit();
    try testing.expectEqual(@as(usize, 2), st.sets.items.len);
}

test "af: floating acceptance — d preferred-skeptical but not grounded" {
    // a↔b, both attack c, c attacks d.
    const af = Af{ .n = 4, .attacks = &.{
        .{ 0, 1 }, .{ 1, 0 }, .{ 0, 2 }, .{ 1, 2 }, .{ 2, 3 },
    } };
    try testing.expectEqual(@as(u32, 0), grounded(af));
    try testing.expect(try accepted(testing.allocator, af, 3, .preferred, .skeptical));
    try testing.expect(!try accepted(testing.allocator, af, 2, .preferred, .credulous));
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    try testing.expectEqual(@as(usize, 2), pr.sets.items.len);
    try testing.expect(pr.contains(mask(&.{ 0, 3 })) and pr.contains(mask(&.{ 1, 3 })));
}

test "af: grounded is a complete extension and included in every preferred" {
    const af = Af{ .n = 5, .attacks = &.{
        .{ 0, 1 }, .{ 1, 2 }, .{ 2, 3 }, .{ 3, 4 }, .{ 4, 2 },
    } };
    const g = grounded(af);
    var co = try extensions(testing.allocator, af, .complete);
    defer co.deinit();
    try testing.expect(co.contains(g));
    var pr = try extensions(testing.allocator, af, .preferred);
    defer pr.deinit();
    for (pr.sets.items) |p| {
        try testing.expect((g & p) == g);
    }
}
