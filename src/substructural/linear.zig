//! Linear logic (intuitionistic fragment ILL) — resource-sensitive connectives.
//!
//! Connectives:
//!   A ⊗ B   multiplicative conjunction (times) — consume both
//!   A ⊸ B   linear implication (lolli) — consume A to produce B
//!   A & B   additive conjunction (with) — choose one
//!   A ⊕ B   additive disjunction (plus)
//!   !A      exponential (of course) — unrestricted reuse
//!   1, ⊤, 0 units
//!
//! Fragment: formula AST + linear context multiset + a resource-counting
//! checker for ⊗/⊸ introduction patterns. Not a full focusing prover.

const std = @import("std");

pub const Formula = union(enum) {
    atom: []const u8,
    one, // 1
    top, // ⊤
    zero, // 0
    tensor: struct { l: *Formula, r: *Formula }, // ⊗
    with: struct { l: *Formula, r: *Formula }, // &
    plus: struct { l: *Formula, r: *Formula }, // ⊕
    lolli: struct { l: *Formula, r: *Formula }, // ⊸
    of_course: *Formula, // !
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

pub fn formulaEql(a: *const Formula, b: *const Formula) bool {
    return switch (a.*) {
        .atom => |x| switch (b.*) {
            .atom => |y| std.mem.eql(u8, x, y),
            else => false,
        },
        .one => b.* == .one,
        .top => b.* == .top,
        .zero => b.* == .zero,
        .tensor => |x| switch (b.*) {
            .tensor => |y| formulaEql(x.l, y.l) and formulaEql(x.r, y.r),
            else => false,
        },
        .with => |x| switch (b.*) {
            .with => |y| formulaEql(x.l, y.l) and formulaEql(x.r, y.r),
            else => false,
        },
        .plus => |x| switch (b.*) {
            .plus => |y| formulaEql(x.l, y.l) and formulaEql(x.r, y.r),
            else => false,
        },
        .lolli => |x| switch (b.*) {
            .lolli => |y| formulaEql(x.l, y.l) and formulaEql(x.r, y.r),
            else => false,
        },
        .of_course => |x| switch (b.*) {
            .of_course => |y| formulaEql(x, y),
            else => false,
        },
    };
}

/// Multiset of formulas as a bag of atom counts (only atoms for the spine).
pub const LinearCtx = struct {
    /// atom name → count
    counts: std.StringHashMap(u32),

    pub fn init(allocator: std.mem.Allocator) LinearCtx {
        return .{ .counts = std.StringHashMap(u32).init(allocator) };
    }
    pub fn deinit(self: *LinearCtx) void {
        self.counts.deinit();
        self.* = undefined;
    }
    pub fn add(self: *LinearCtx, name: []const u8, n: u32) !void {
        const gop = try self.counts.getOrPut(name);
        if (!gop.found_existing) gop.value_ptr.* = 0;
        gop.value_ptr.* += n;
    }
    pub fn consume(self: *LinearCtx, name: []const u8, n: u32) bool {
        const v = self.counts.get(name) orelse return false;
        if (v < n) return false;
        if (v == n) {
            _ = self.counts.remove(name);
        } else {
            self.counts.put(name, v - n) catch {};
        }
        return true;
    }
    pub fn total(self: *const LinearCtx) u32 {
        var s: u32 = 0;
        var it = self.counts.valueIterator();
        while (it.next()) |v| s += v.*;
        return s;
    }
};

/// Check that a ⊗ of atoms can be formed exactly from the context (no surplus).
pub fn checkTensorExact(ctx: *LinearCtx, atoms: []const []const u8) bool {
    for (atoms) |a| {
        if (!ctx.consume(a, 1)) return false;
    }
    return ctx.total() == 0;
}

test "linear resource exact consume" {
    var ctx = LinearCtx.init(std.testing.allocator);
    defer ctx.deinit();
    try ctx.add("A", 1);
    try ctx.add("B", 1);
    try std.testing.expect(checkTensorExact(&ctx, &[_][]const u8{ "A", "B" }));
}

test "linear resource surplus fails" {
    var ctx = LinearCtx.init(std.testing.allocator);
    defer ctx.deinit();
    try ctx.add("A", 2);
    try ctx.add("B", 1);
    try std.testing.expect(!checkTensorExact(&ctx, &[_][]const u8{ "A", "B" }));
}

test "lolli formula shape" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = "A" });
    const b = try arena.f(.{ .atom = "B" });
    const l = try arena.f(.{ .lolli = .{ .l = a, .r = b } });
    try std.testing.expect(l.* == .lolli);
}
