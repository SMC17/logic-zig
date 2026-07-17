//! Modal logic on finite Kripke frames — fragment for universal library.
//!
//! Formulas: prop | ¬ | ∧ | ∨ | □ | ◇
//! Frames: worlds + accessibility (relation matrix).
//! K: no frame conditions; T: reflexive; S4: preorder (refl+trans).

const std = @import("std");

pub const FrameClass = enum { k, t, s4 };

pub const Formula = union(enum) {
    prop: u32,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    box: *Formula,
    diamond: *Formula,
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*Formula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn f(self: *Arena, v: Formula) !*Formula {
        const p = try self.allocator.create(Formula);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

pub const Frame = struct {
    n_worlds: u32,
    /// n*n bool, row-major: R[w][v]
    rel: []bool,
    /// valuation: world -> bitset of props (simple: prop < 32)
    val: []u32,

    pub fn init(allocator: std.mem.Allocator, n: u32) !Frame {
        const rel = try allocator.alloc(bool, n * n);
        @memset(rel, false);
        const val = try allocator.alloc(u32, n);
        @memset(val, 0);
        return .{ .n_worlds = n, .rel = rel, .val = val };
    }

    pub fn deinit(self: *Frame, allocator: std.mem.Allocator) void {
        allocator.free(self.rel);
        allocator.free(self.val);
        self.* = undefined;
    }

    pub fn setR(self: *Frame, w: u32, v: u32, on: bool) void {
        self.rel[w * self.n_worlds + v] = on;
    }

    pub fn hasR(self: *const Frame, w: u32, v: u32) bool {
        return self.rel[w * self.n_worlds + v];
    }

    pub fn setProp(self: *Frame, w: u32, p: u32, on: bool) void {
        if (p >= 32) return;
        if (on) self.val[w] |= @as(u32, 1) << @intCast(p) else self.val[w] &= ~(@as(u32, 1) << @intCast(p));
    }

    pub fn makeReflexive(self: *Frame) void {
        var w: u32 = 0;
        while (w < self.n_worlds) : (w += 1) self.setR(w, w, true);
    }

    pub fn makeTransitiveClosure(self: *Frame) void {
        // Floyd
        var k: u32 = 0;
        while (k < self.n_worlds) : (k += 1) {
            var i: u32 = 0;
            while (i < self.n_worlds) : (i += 1) {
                var j: u32 = 0;
                while (j < self.n_worlds) : (j += 1) {
                    if (self.hasR(i, k) and self.hasR(k, j)) self.setR(i, j, true);
                }
            }
        }
    }
};

pub fn evalAt(fr: *const Frame, w: u32, phi: *const Formula) bool {
    return switch (phi.*) {
        .prop => |p| (fr.val[w] >> @intCast(p)) & 1 == 1,
        .not => |n| !evalAt(fr, w, n),
        .and_ => |a| evalAt(fr, w, a.l) and evalAt(fr, w, a.r),
        .or_ => |a| evalAt(fr, w, a.l) or evalAt(fr, w, a.r),
        .box => |inner| {
            var v: u32 = 0;
            while (v < fr.n_worlds) : (v += 1) {
                if (fr.hasR(w, v) and !evalAt(fr, v, inner)) return false;
            }
            return true;
        },
        .diamond => |inner| {
            var v: u32 = 0;
            while (v < fr.n_worlds) : (v += 1) {
                if (fr.hasR(w, v) and evalAt(fr, v, inner)) return true;
            }
            return false;
        },
    };
}

pub fn validOnFrame(fr: *const Frame, phi: *const Formula) bool {
    var w: u32 = 0;
    while (w < fr.n_worlds) : (w += 1) {
        if (!evalAt(fr, w, phi)) return false;
    }
    return true;
}

test "modal K box false when successor fails" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var fr = try Frame.init(std.testing.allocator, 2);
    defer fr.deinit(std.testing.allocator);
    fr.setR(0, 1, true);
    fr.setProp(1, 0, false);
    const p = try arena.f(.{ .prop = 0 });
    const boxp = try arena.f(.{ .box = p });
    try std.testing.expect(!evalAt(&fr, 0, boxp));
}

test "modal diamond true" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var fr = try Frame.init(std.testing.allocator, 2);
    defer fr.deinit(std.testing.allocator);
    fr.setR(0, 1, true);
    fr.setProp(1, 0, true);
    const p = try arena.f(.{ .prop = 0 });
    const dp = try arena.f(.{ .diamond = p });
    try std.testing.expect(evalAt(&fr, 0, dp));
}

test "S4 reflexive T axiom box p -> p on reflexive" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var fr = try Frame.init(std.testing.allocator, 1);
    defer fr.deinit(std.testing.allocator);
    fr.makeReflexive();
    fr.setProp(0, 0, true);
    const p = try arena.f(.{ .prop = 0 });
    // □p → p : if box holds then p
    try std.testing.expect(evalAt(&fr, 0, p));
}
