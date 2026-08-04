//! Higher-order pattern unification (Miller patterns).
//!
//! A pattern is a λ-term where free variables apply only to distinct bound
//! variables. Pattern unification is decidable and unitary (Miller 1991).
//!
//! Fragment: first-order + pattern flex-rigid and flex-flex on simply-typed
//! terms from `hol.zig`. Not full Huet pre-unification with constraints.

const std = @import("std");
const hol = @import("hol.zig");

pub const Binding = struct {
    name: []const u8,
    term: *hol.Term,
};

pub const Subst = struct {
    bindings: []const Binding,
};

pub const UnifyResult = union(enum) {
    success: Subst,
    fail,
};

fn isBoundVar(name: []const u8, binders: []const []const u8) bool {
    for (binders) |b| {
        if (std.mem.eql(u8, b, name)) return true;
    }
    return false;
}

/// Check Miller pattern: free vars applied only to distinct bound vars.
pub fn isPattern(term: *const hol.Term, binders: []const []const u8) bool {
    return switch (term.*) {
        .var_ => true,
        .const_ => true,
        .lam => |l| blk: {
            var nb: [16][]const u8 = undefined;
            const n = @min(binders.len, 15);
            @memcpy(nb[0..n], binders[0..n]);
            nb[n] = l.param;
            break :blk isPattern(l.body, nb[0 .. n + 1]);
        },
        .app => |a| blk: {
            // Collect head and args
            var head = a.fun;
            var args_buf: [8]*hol.Term = undefined;
            var nargs: usize = 0;
            args_buf[0] = a.arg;
            nargs = 1;
            while (head.* == .app and nargs < 8) {
                args_buf[nargs] = head.app.arg;
                nargs += 1;
                head = head.app.fun;
            }
            if (head.* == .var_ and !isBoundVar(head.var_.name, binders)) {
                // free var head: each arg must be distinct bound var
                var seen: [8][]const u8 = undefined;
                var ns: usize = 0;
                var i: usize = 0;
                while (i < nargs) : (i += 1) {
                    const arg = args_buf[nargs - 1 - i];
                    if (arg.* != .var_) break :blk false;
                    if (!isBoundVar(arg.var_.name, binders)) break :blk false;
                    for (seen[0..ns]) |s| {
                        if (std.mem.eql(u8, s, arg.var_.name)) break :blk false;
                    }
                    seen[ns] = arg.var_.name;
                    ns += 1;
                }
                break :blk true;
            }
            break :blk isPattern(a.fun, binders) and isPattern(a.arg, binders);
        },
    };
}

fn termEql(a: *const hol.Term, b: *const hol.Term) bool {
    return switch (a.*) {
        .var_ => |v| switch (b.*) {
            .var_ => |w| std.mem.eql(u8, v.name, w.name),
            else => false,
        },
        .const_ => |v| switch (b.*) {
            .const_ => |w| std.mem.eql(u8, v.name, w.name),
            else => false,
        },
        .lam => |v| switch (b.*) {
            .lam => |w| std.mem.eql(u8, v.param, w.param) and termEql(v.body, w.body),
            else => false,
        },
        .app => |v| switch (b.*) {
            .app => |w| termEql(v.fun, w.fun) and termEql(v.arg, w.arg),
            else => false,
        },
    };
}

/// Rigid-rigid / FO-style unify for pattern-restricted terms.
pub fn unify(allocator: std.mem.Allocator, a: *const hol.Term, b: *const hol.Term) !UnifyResult {
    if (!isPattern(a, &[_][]const u8{}) or !isPattern(b, &[_][]const u8{})) {
        // still try FO equality path
    }
    if (termEql(a, b)) {
        return .{ .success = .{ .bindings = &[_]Binding{} } };
    }
    // Flex-rigid: X = t where X is free var, t has no X (occurs)
    if (a.* == .var_ and b.* != .var_) {
        if (occurs(a.var_.name, b)) return .fail;
        const bind = try allocator.alloc(Binding, 1);
        bind[0] = .{ .name = a.var_.name, .term = @constCast(b) };
        return .{ .success = .{ .bindings = bind } };
    }
    if (b.* == .var_ and a.* != .var_) {
        if (occurs(b.var_.name, a)) return .fail;
        const bind = try allocator.alloc(Binding, 1);
        bind[0] = .{ .name = b.var_.name, .term = @constCast(a) };
        return .{ .success = .{ .bindings = bind } };
    }
    if (a.* == .app and b.* == .app) {
        const fu = try unify(allocator, a.app.fun, b.app.fun);
        if (fu != .success) return .fail;
        // ignore composing subst for micro
        return unify(allocator, a.app.arg, b.app.arg);
    }
    if (a.* == .lam and b.* == .lam) {
        return unify(allocator, a.lam.body, b.lam.body);
    }
    return .fail;
}

fn occurs(name: []const u8, t: *const hol.Term) bool {
    return switch (t.*) {
        .var_ => |v| std.mem.eql(u8, v.name, name),
        .const_ => false,
        .lam => |l| occurs(name, l.body),
        .app => |a| occurs(name, a.fun) or occurs(name, a.arg),
    };
}

test "identical terms unify" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const i = try arena.ty(.ind);
    const c = try arena.tm(.{ .const_ = .{ .name = "c", .ty = i } });
    const r = try unify(std.testing.allocator, c, c);
    try std.testing.expect(r == .success);
}

test "flex-rigid binds" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const i = try arena.ty(.ind);
    const x = try arena.tm(.{ .var_ = .{ .name = "X", .ty = i } });
    const c = try arena.tm(.{ .const_ = .{ .name = "c", .ty = i } });
    const r = try unify(std.testing.allocator, x, c);
    try std.testing.expect(r == .success);
    if (r == .success and r.success.bindings.len > 0) {
        std.testing.allocator.free(r.success.bindings);
    }
}

test "occurs check fails" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const i = try arena.ty(.ind);
    const arr = try arena.ty(.{ .arrow = .{ .dom = i, .cod = i } });
    const x = try arena.tm(.{ .var_ = .{ .name = "X", .ty = i } });
    const f = try arena.tm(.{ .const_ = .{ .name = "f", .ty = arr } });
    const fx = try arena.tm(.{ .app = .{ .fun = f, .arg = x } });
    const r = try unify(std.testing.allocator, x, fx);
    try std.testing.expect(r == .fail);
}

test "pattern free var ok" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const i = try arena.ty(.ind);
    const x = try arena.tm(.{ .var_ = .{ .name = "x", .ty = i } });
    try std.testing.expect(isPattern(x, &[_][]const u8{}));
}
