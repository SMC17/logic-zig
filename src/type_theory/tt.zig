//! Martin-Löf style type theory — micro kernel (universal library spine).
//!
//! Judgments: Γ ⊢ t : T  (check only; no full elaborator / universe hierarchy).
//! Types: base, pi (non-dependent for micro), sigma (pair), Id (identity type).
//! Terms: var, lam, app, pair, refl.
//!
//! This is intentionally a **skeleton/fragment** toward a proof assistant,
//! not Lean/Coq parity.

const std = @import("std");

pub const Name = []const u8;

pub const Ty = union(enum) {
    base: Name,
    pi: struct { dom: *Ty, cod: *Ty },
    sigma: struct { fst: *Ty, snd: *Ty },
    id: struct { ty: *Ty }, // Id_A (endpoints implicit in micro)
    unit,
};

pub const Tm = union(enum) {
    var_: u32, // de Bruijn
    lam: *Tm,
    app: struct { fun: *Tm, arg: *Tm },
    pair: struct { fst: *Tm, snd: *Tm },
    refl,
    star,
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    types: std.ArrayList(*Ty) = .empty,
    terms: std.ArrayList(*Tm) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Arena) void {
        for (self.types.items) |t| self.allocator.destroy(t);
        for (self.terms.items) |t| self.allocator.destroy(t);
        self.types.deinit(self.allocator);
        self.terms.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn ty(self: *Arena, v: Ty) !*Ty {
        const p = try self.allocator.create(Ty);
        p.* = v;
        try self.types.append(self.allocator, p);
        return p;
    }

    pub fn tm(self: *Arena, v: Tm) !*Tm {
        const p = try self.allocator.create(Tm);
        p.* = v;
        try self.terms.append(self.allocator, p);
        return p;
    }
};

pub const Ctx = struct {
    /// Type of variables (de Bruijn level: index 0 is most recent).
    binders: std.ArrayList(*Ty) = .empty,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Ctx {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Ctx) void {
        self.binders.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn push(self: *Ctx, t: *Ty) !void {
        try self.binders.append(self.allocator, t);
    }

    pub fn pop(self: *Ctx) void {
        _ = self.binders.pop();
    }

    pub fn lookup(self: *const Ctx, i: u32) ?*Ty {
        if (i >= self.binders.items.len) return null;
        return self.binders.items[self.binders.items.len - 1 - i];
    }
};

fn tyEq(a: *const Ty, b: *const Ty) bool {
    return switch (a.*) {
        .base => |n| switch (b.*) {
            .base => |m| std.mem.eql(u8, n, m),
            else => false,
        },
        .unit => b.* == .unit,
        .id => |ia| switch (b.*) {
            .id => |ib| tyEq(ia.ty, ib.ty),
            else => false,
        },
        .pi => |pa| switch (b.*) {
            .pi => |pb| tyEq(pa.dom, pb.dom) and tyEq(pa.cod, pb.cod),
            else => false,
        },
        .sigma => |sa| switch (b.*) {
            .sigma => |sb| tyEq(sa.fst, sb.fst) and tyEq(sa.snd, sb.snd),
            else => false,
        },
    };
}

/// Check Γ ⊢ t : T. Returns false on failure (no fancy errors yet).
pub fn check(ctx: *Ctx, t: *const Tm, expected: *const Ty) bool {
    switch (t.*) {
        .var_ => |i| {
            const got = ctx.lookup(i) orelse return false;
            return tyEq(got, expected);
        },
        .star => return expected.* == .unit,
        .refl => return switch (expected.*) {
            .id => true,
            else => false,
        },
        .lam => |body| {
            return switch (expected.*) {
                .pi => |p| {
                    ctx.push(p.dom) catch return false;
                    defer ctx.pop();
                    return check(ctx, body, p.cod);
                },
                else => false,
            };
        },
        .app => |a| {
            // Infer fun as Pi? Micro: only check if we can invent — require expected matches cod after checking arg against any pi
            // Simplified: reject unless we extend with synth. Use synth for app.
            _ = a;
            return false; // use synth
        },
        .pair => |pr| {
            return switch (expected.*) {
                .sigma => |s| check(ctx, pr.fst, s.fst) and check(ctx, pr.snd, s.snd),
                else => false,
            };
        },
    }
}

/// Synthesize type of a term (partial).
pub fn synth(ctx: *Ctx, t: *const Tm) ?*const Ty {
    return switch (t.*) {
        .var_ => |i| ctx.lookup(i),
        .star => null, // need arena for unit pointer — caller checks unit
        .refl => null,
        .lam => null, // need annotation
        .app => null, // incomplete micro
        .pair => null,
    };
}

test "tt var and unit" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var ctx = Ctx.init(std.testing.allocator);
    defer ctx.deinit();
    const nat = try arena.ty(.{ .base = "Nat" });
    try ctx.push(nat);
    const v0 = try arena.tm(.{ .var_ = 0 });
    try std.testing.expect(check(&ctx, v0, nat));
    const u = try arena.ty(.unit);
    const st = try arena.tm(.star);
    try std.testing.expect(check(&ctx, st, u));
}

test "tt identity refl" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var ctx = Ctx.init(std.testing.allocator);
    defer ctx.deinit();
    const nat = try arena.ty(.{ .base = "Nat" });
    const idn = try arena.ty(.{ .id = .{ .ty = nat } });
    const r = try arena.tm(.refl);
    try std.testing.expect(check(&ctx, r, idn));
}

test "tt lambda pi" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var ctx = Ctx.init(std.testing.allocator);
    defer ctx.deinit();
    const a = try arena.ty(.{ .base = "A" });
    // identity λx.x : A→A
    const pi_id = try arena.ty(.{ .pi = .{ .dom = a, .cod = a } });
    const body = try arena.tm(.{ .var_ = 0 });
    const lam = try arena.tm(.{ .lam = body });
    try std.testing.expect(check(&ctx, lam, pi_id));
}
