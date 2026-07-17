//! Robinson unification with occurs check.

const std = @import("std");
const term_mod = @import("term.zig");
const TermPool = term_mod.TermPool;
const TermId = term_mod.TermId;

pub const Subst = struct {
    allocator: std.mem.Allocator,
    /// var term index → term
    map: std.AutoHashMapUnmanaged(u32, TermId) = .{},

    pub fn init(allocator: std.mem.Allocator) Subst {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Subst) void {
        self.map.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn get(self: *const Subst, v: TermId) ?TermId {
        return self.map.get(v.index());
    }

    pub fn put(self: *Subst, v: TermId, t: TermId) !void {
        try self.map.put(self.allocator, v.index(), t);
    }

    /// Chase variable bindings.
    pub fn deref(self: *const Subst, pool: *const TermPool, t: TermId) TermId {
        var cur = t;
        var guard: u32 = 0;
        while (pool.isVar(cur)) : (guard += 1) {
            if (guard > 10_000) break;
            if (self.get(cur)) |n| {
                cur = n;
            } else break;
        }
        return cur;
    }
};

pub const UnifyError = error{
    Clash,
    Occurs,
    OccursCheck,
} || std.mem.Allocator.Error;

pub fn unify(pool: *const TermPool, subst: *Subst, t1: TermId, t2: TermId) UnifyError!void {
    const a = subst.deref(pool, t1);
    const b = subst.deref(pool, t2);
    if (a == b) return;

    if (pool.isVar(a)) {
        if (occurs(pool, subst, a, b)) return error.OccursCheck;
        try subst.put(a, b);
        return;
    }
    if (pool.isVar(b)) {
        if (occurs(pool, subst, b, a)) return error.OccursCheck;
        try subst.put(b, a);
        return;
    }

    // Both non-var
    if (pool.tag(a) != pool.tag(b)) return error.Clash;
    if (!std.mem.eql(u8, pool.nameOf(a), pool.nameOf(b))) return error.Clash;

    if (pool.tag(a) == .constant) return; // same name

    // func
    const aa = pool.argsOf(a);
    const bb = pool.argsOf(b);
    if (aa.len != bb.len) return error.Clash;
    for (aa, bb) |x, y| {
        try unify(pool, subst, x, y);
    }
}

fn occurs(pool: *const TermPool, subst: *const Subst, v: TermId, t: TermId) bool {
    const d = subst.deref(pool, t);
    if (d == v) return true;
    if (pool.tag(d) == .func) {
        for (pool.argsOf(d)) |arg| {
            if (occurs(pool, subst, v, arg)) return true;
        }
    }
    return false;
}

/// Apply substitution to term (rebuild).
pub fn apply(pool: *TermPool, subst: *const Subst, t: TermId) !TermId {
    const d = subst.deref(pool, t);
    if (pool.tag(d) != .func) return d;
    const args = pool.argsOf(d);
    var new_args: std.ArrayList(TermId) = .empty;
    defer new_args.deinit(pool.allocator);
    for (args) |a| {
        try new_args.append(pool.allocator, try apply(pool, subst, a));
    }
    return try pool.mkFunc(pool.nameOf(d), new_args.items);
}

test "unify f(x,g(y)) with f(a,g(b))" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const x = try pool.mkVar("x");
    const y = try pool.mkVar("y");
    const a = try pool.mkConst("a");
    const b = try pool.mkConst("b");
    const gy = try pool.mkFunc("g", &.{y});
    const gb = try pool.mkFunc("g", &.{b});
    const t1 = try pool.mkFunc("f", &.{ x, gy });
    const t2 = try pool.mkFunc("f", &.{ a, gb });

    var subst = Subst.init(std.testing.allocator);
    defer subst.deinit();
    try unify(&pool, &subst, t1, t2);
    try std.testing.expect(subst.deref(&pool, x) == a);
    try std.testing.expect(subst.deref(&pool, y) == b);
}

test "occurs check" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const x = try pool.mkVar("x");
    const x2 = try pool.mkVar("x"); // same id
    try std.testing.expect(x == x2);
    const fx = try pool.mkFunc("f", &.{x});
    var subst = Subst.init(std.testing.allocator);
    defer subst.deinit();
    try std.testing.expectError(error.OccursCheck, unify(&pool, &subst, x, fx));
}
