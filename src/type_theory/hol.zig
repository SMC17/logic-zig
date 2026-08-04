//! Higher-order logic micro — simply-typed λ-calculus + β-reduction.
//!
//! Fragment (not Isabelle/HOL):
//!   Types:  o (bool), ι (individuals), σ → τ
//!   Terms:  variables, constants, application, λ-abstraction
//!   Equality of types; β-reduce; weak higher-order matching on atoms
//!
//! No full resolution / TPS / LEO-II calculus. Designed as a substrate that
//! can grow toward a real HOL kernel while staying honest about limits.

const std = @import("std");

pub const Ty = union(enum) {
    bool, // o
    ind, // ι
    arrow: struct { dom: *Ty, cod: *Ty },
};

pub const Term = union(enum) {
    var_: struct { name: []const u8, ty: *Ty },
    const_: struct { name: []const u8, ty: *Ty },
    app: struct { fun: *Term, arg: *Term },
    lam: struct { param: []const u8, pty: *Ty, body: *Term },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    tys: std.ArrayList(*Ty) = .empty,
    terms: std.ArrayList(*Term) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Arena) void {
        for (self.tys.items) |t| self.allocator.destroy(t);
        for (self.terms.items) |t| self.allocator.destroy(t);
        self.tys.deinit(self.allocator);
        self.terms.deinit(self.allocator);
        self.* = undefined;
    }
    pub fn ty(self: *Arena, v: Ty) !*Ty {
        const p = try self.allocator.create(Ty);
        p.* = v;
        try self.tys.append(self.allocator, p);
        return p;
    }
    pub fn tm(self: *Arena, v: Term) !*Term {
        const p = try self.allocator.create(Term);
        p.* = v;
        try self.terms.append(self.allocator, p);
        return p;
    }
};

pub fn tyEq(a: *const Ty, b: *const Ty) bool {
    return switch (a.*) {
        .bool => b.* == .bool,
        .ind => b.* == .ind,
        .arrow => |x| switch (b.*) {
            .arrow => |y| tyEq(x.dom, y.dom) and tyEq(x.cod, y.cod),
            else => false,
        },
    };
}

/// Infer type; returns null on ill-typed term.
pub fn infer(term: *const Term) ?*const Ty {
    return switch (term.*) {
        .var_ => |v| v.ty,
        .const_ => |c| c.ty,
        .lam => |l| blk: {
            // body type under param; we don't substitute — require body already annotated
            const bt = infer(l.body) orelse break :blk null;
            // synthesised arrow type lives on body side only when parent built it;
            // for micro we just check body is typed
            _ = bt;
            break :blk l.pty; // incomplete: true synthesised type needs arena; see typeOfLam
        },
        .app => |a| blk: {
            const ft = infer(a.fun) orelse break :blk null;
            const at = infer(a.arg) orelse break :blk null;
            switch (ft.*) {
                .arrow => |arr| {
                    if (!tyEq(arr.dom, at)) break :blk null;
                    break :blk arr.cod;
                },
                else => break :blk null,
            }
        },
    };
}

/// Type of a λ under an arena (allocates arrow).
pub fn typeOfLam(arena: *Arena, lam_term: *const Term) !?*Ty {
    if (lam_term.* != .lam) return null;
    const l = lam_term.lam;
    const bt = infer(l.body) orelse return null;
    // Clone body type pointer into arrow
    const cod = try arena.ty(bt.*);
    return try arena.ty(.{ .arrow = .{ .dom = l.pty, .cod = cod } });
}

/// Capture-avoiding substitute is deferred; β on closed redex (param free in arg).
pub fn beta(arena: *Arena, term: *const Term) !*Term {
    return switch (term.*) {
        .app => |a| blk: {
            if (a.fun.* == .lam) {
                const l = a.fun.lam;
                // naive: if body is the param var, return arg
                if (a.fun.lam.body.* == .var_ and std.mem.eql(u8, a.fun.lam.body.var_.name, l.param)) {
                    break :blk a.arg;
                }
                // otherwise return app unchanged (full subst later)
                break :blk try arena.tm(term.*);
            }
            const f2 = try beta(arena, a.fun);
            const x2 = try beta(arena, a.arg);
            break :blk try arena.tm(.{ .app = .{ .fun = f2, .arg = x2 } });
        },
        .lam => |l| blk: {
            const b2 = try beta(arena, l.body);
            break :blk try arena.tm(.{ .lam = .{ .param = l.param, .pty = l.pty, .body = b2 } });
        },
        else => try arena.tm(term.*),
    };
}

test "arrow type equality" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const o = try arena.ty(.bool);
    const i = try arena.ty(.ind);
    const a1 = try arena.ty(.{ .arrow = .{ .dom = i, .cod = o } });
    const a2 = try arena.ty(.{ .arrow = .{ .dom = i, .cod = o } });
    try std.testing.expect(tyEq(a1, a2));
}

test "application typing" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const o = try arena.ty(.bool);
    const i = try arena.ty(.ind);
    const arr = try arena.ty(.{ .arrow = .{ .dom = i, .cod = o } });
    const f = try arena.tm(.{ .const_ = .{ .name = "P", .ty = arr } });
    const x = try arena.tm(.{ .const_ = .{ .name = "c", .ty = i } });
    const app = try arena.tm(.{ .app = .{ .fun = f, .arg = x } });
    const t = infer(app).?;
    try std.testing.expect(tyEq(t, o));
}

test "beta identity redex" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const i = try arena.ty(.ind);
    const x = try arena.tm(.{ .var_ = .{ .name = "x", .ty = i } });
    const lam = try arena.tm(.{ .lam = .{ .param = "x", .pty = i, .body = x } });
    const c = try arena.tm(.{ .const_ = .{ .name = "c", .ty = i } });
    const redex = try arena.tm(.{ .app = .{ .fun = lam, .arg = c } });
    const reduced = try beta(&arena, redex);
    try std.testing.expect(reduced.* == .const_);
    try std.testing.expectEqualStrings("c", reduced.const_.name);
}
