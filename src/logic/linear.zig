//! Linear logic — the multiplicative fragment (MLL with units).
//!
//! One-sided sequent calculus over negation normal form:
//!
//!   ax  ⊢ a, a⊥          1  ⊢ 1
//!   ⅋   ⊢ Γ,A,B ⇒ ⊢ Γ,A⅋B      (invertible)
//!   ⊥   ⊢ Γ ⇒ ⊢ Γ,⊥            (invertible)
//!   ⊗   ⊢ Γ,A and ⊢ Δ,B ⇒ ⊢ Γ,Δ,A⊗B   (context split — resources divided)
//!
//! No weakening, no contraction: assumptions are consumed exactly once.
//! Provability is decided by applying invertible rules to saturation, then
//! exhaustively splitting contexts at each ⊗ (exact; exponential in context
//! size — MLL provability is NP-complete, this is the small-sequent slice).
//!
//! A ⊸ B is sugar for A⊥ ⅋ B. Canon: identity provable; weakening
//! (A⊗B ⊸ A) and contraction (A ⊸ A⊗A) both refuted — the substructural
//! signature — and every provable sequent satisfies MLL's balanced-atom
//! counting invariant (checked on random formulas).

const std = @import("std");

pub const Formula = union(enum) {
    pos: u32, // atom a
    negA: u32, // a⊥
    tensor: [2]*const Formula,
    par: [2]*const Formula,
    one, // 1
    bot, // ⊥
};

pub const Builder = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .arena = std.heap.ArenaAllocator.init(allocator) };
    }
    pub fn deinit(self: *Builder) void {
        self.arena.deinit();
    }
    fn mk(self: *Builder, f: Formula) *const Formula {
        const p = self.arena.allocator().create(Formula) catch @panic("oom");
        p.* = f;
        return p;
    }
    pub fn atom(self: *Builder, i: u32) *const Formula {
        return self.mk(.{ .pos = i });
    }
    pub fn negAtom(self: *Builder, i: u32) *const Formula {
        return self.mk(.{ .negA = i });
    }
    pub fn tensorF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .tensor = .{ a, b } });
    }
    pub fn parF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .par = .{ a, b } });
    }
    pub fn oneF(self: *Builder) *const Formula {
        return self.mk(.one);
    }
    pub fn botF(self: *Builder) *const Formula {
        return self.mk(.bot);
    }

    /// Linear negation (involutive, De Morgan over ⊗/⅋, 1/⊥).
    pub fn dual(self: *Builder, f: *const Formula) *const Formula {
        return switch (f.*) {
            .pos => |i| self.negAtom(i),
            .negA => |i| self.atom(i),
            .tensor => |p| self.parF(self.dual(p[0]), self.dual(p[1])),
            .par => |p| self.tensorF(self.dual(p[0]), self.dual(p[1])),
            .one => self.botF(),
            .bot => self.oneF(),
        };
    }

    /// A ⊸ B := A⊥ ⅋ B.
    pub fn lolli(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.parF(self.dual(a), b);
    }
};

const Ctx = []const *const Formula;

fn without(allocator: std.mem.Allocator, ctx: Ctx, drop: usize, extra: []const *const Formula) ![]*const Formula {
    const out = try allocator.alloc(*const Formula, ctx.len - 1 + extra.len);
    var k: usize = 0;
    for (ctx, 0..) |f, i| {
        if (i == drop) continue;
        out[k] = f;
        k += 1;
    }
    for (extra) |f| {
        out[k] = f;
        k += 1;
    }
    return out;
}

fn proveCtx(allocator: std.mem.Allocator, ctx: Ctx) error{OutOfMemory}!bool {
    // Invertible rules first: ⅋ and ⊥.
    for (ctx, 0..) |f, i| {
        switch (f.*) {
            .par => |p| {
                const c = try without(allocator, ctx, i, &.{ p[0], p[1] });
                defer allocator.free(c);
                return proveCtx(allocator, c);
            },
            .bot => {
                const c = try without(allocator, ctx, i, &.{});
                defer allocator.free(c);
                return proveCtx(allocator, c);
            },
            else => {},
        }
    }
    // Axioms.
    if (ctx.len == 1 and ctx[0].* == .one) return true;
    if (ctx.len == 2) {
        const a = ctx[0];
        const c = ctx[1];
        const ax = switch (a.*) {
            .pos => |i| c.* == .negA and c.negA == i,
            .negA => |i| c.* == .pos and c.pos == i,
            else => false,
        };
        if (ax) return true;
    }
    // ⊗: choose a principal tensor and split the rest of the context.
    for (ctx, 0..) |f, i| {
        switch (f.*) {
            .tensor => |p| {
                // Others = ctx without i; enumerate all subset splits.
                var others = try allocator.alloc(*const Formula, ctx.len - 1);
                defer allocator.free(others);
                var k: usize = 0;
                for (ctx, 0..) |g, j| {
                    if (j != i) {
                        others[k] = g;
                        k += 1;
                    }
                }
                const n = others.len;
                std.debug.assert(n <= 20);
                const total: u32 = @as(u32, 1) << @intCast(n);
                var mask: u32 = 0;
                while (mask < total) : (mask += 1) {
                    var left: std.ArrayList(*const Formula) = .empty;
                    defer left.deinit(allocator);
                    var right: std.ArrayList(*const Formula) = .empty;
                    defer right.deinit(allocator);
                    for (others, 0..) |g, j| {
                        if ((mask >> @intCast(j)) & 1 == 1) {
                            try left.append(allocator, g);
                        } else {
                            try right.append(allocator, g);
                        }
                    }
                    try left.append(allocator, p[0]);
                    try right.append(allocator, p[1]);
                    if (try proveCtx(allocator, left.items) and try proveCtx(allocator, right.items)) {
                        return true;
                    }
                }
            },
            else => {},
        }
    }
    return false;
}

/// Is ⊢ f provable in MLL?
pub fn provable(allocator: std.mem.Allocator, f: *const Formula) !bool {
    return proveCtx(allocator, &.{f});
}

/// MLL counting invariant: per atom, #positive == #negative occurrences.
/// Necessary for provability (not sufficient).
pub fn balanced(f: *const Formula) bool {
    var pos = [_]i32{0} ** 32;
    countAtoms(f, &pos);
    for (pos) |c| {
        if (c != 0) return false;
    }
    return true;
}

fn countAtoms(f: *const Formula, acc: *[32]i32) void {
    switch (f.*) {
        .pos => |i| acc[i] += 1,
        .negA => |i| acc[i] -= 1,
        .tensor, .par => |p| {
            countAtoms(p[0], acc);
            countAtoms(p[1], acc);
        },
        .one, .bot => {},
    }
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "mll: identity, symmetry, units" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const a = b.atom(0);
    const c = b.atom(1);
    // ⊢ a ⊸ a
    try testing.expect(try provable(testing.allocator, b.lolli(a, a)));
    // ⊢ (a⊗c) ⊸ (c⊗a)
    try testing.expect(try provable(testing.allocator, b.lolli(b.tensorF(a, c), b.tensorF(c, a))));
    // ⊢ 1, ⊢ ⊥⅋1, ⊢ 1⊗1... (1⊗1 needs both sides ⊢ 1)
    try testing.expect(try provable(testing.allocator, b.oneF()));
    try testing.expect(try provable(testing.allocator, b.parF(b.botF(), b.oneF())));
    try testing.expect(try provable(testing.allocator, b.tensorF(b.oneF(), b.oneF())));
    // Currying: ⊢ (a⊗c ⊸ d) ⊸ (a ⊸ (c ⊸ d))
    const d = b.atom(2);
    try testing.expect(try provable(
        testing.allocator,
        b.lolli(b.lolli(b.tensorF(a, c), d), b.lolli(a, b.lolli(c, d))),
    ));
}

test "mll: weakening and contraction refuted (substructural signature)" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const a = b.atom(0);
    const c = b.atom(1);
    // Weakening: (a⊗c) ⊸ a — must fail (c is discarded).
    try testing.expect(!try provable(testing.allocator, b.lolli(b.tensorF(a, c), a)));
    // Contraction: a ⊸ (a⊗a) — must fail (a is duplicated).
    try testing.expect(!try provable(testing.allocator, b.lolli(a, b.tensorF(a, a))));
    // Exchange is free: (a⊗c) ⊸ (c⊗a) already shown provable.
    // Plain a ⊸ c fails (no connection).
    try testing.expect(!try provable(testing.allocator, b.lolli(a, c)));
    // MIX is not admissible: ⊢ (a⅋a⊥)⊗(c⅋c⊥) provable, but a⊥⅋a⅋c⊥⅋c
    // without the tensor-split is provable too... instead check ax strictness:
    // ⊢ a, a⊥, c, c⊥ as one par-soup is NOT provable (no MIX).
    const soup = b.parF(b.parF(a, b.negAtom(0)), b.parF(c, b.negAtom(1)));
    try testing.expect(!try provable(testing.allocator, soup));
}

test "mll: provable implies balanced atom counts (random)" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var prng = std.Random.DefaultPrng.init(0x11EA);
    const rand = prng.random();
    var provable_count: u32 = 0;
    for (0..300) |_| {
        const f = randomFormula(&b, rand, 3, 2);
        if (try provable(testing.allocator, f)) {
            provable_count += 1;
            try testing.expect(balanced(f));
        }
    }
    // Sanity: the random space does contain provable formulas.
    try testing.expect(provable_count > 0);
}

fn randomFormula(b: *Builder, rand: std.Random, depth: u32, num_atoms: u32) *const Formula {
    if (depth == 0 or rand.uintLessThan(u32, 4) == 0) {
        return switch (rand.uintLessThan(u32, 4)) {
            0 => b.atom(rand.uintLessThan(u32, num_atoms)),
            1 => b.negAtom(rand.uintLessThan(u32, num_atoms)),
            2 => b.oneF(),
            else => b.botF(),
        };
    }
    const l = randomFormula(b, rand, depth - 1, num_atoms);
    const r = randomFormula(b, rand, depth - 1, num_atoms);
    return if (rand.boolean()) b.tensorF(l, r) else b.parF(l, r);
}

test "mll: dual is involutive and lolli chains compose" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const a = b.atom(0);
    const c = b.atom(1);
    const d = b.atom(2);
    // Composition: (a⊸c) ⊗ (c⊸d) ⊸ (a⊸d).
    try testing.expect(try provable(
        testing.allocator,
        b.lolli(b.tensorF(b.lolli(a, c), b.lolli(c, d)), b.lolli(a, d)),
    ));
    // Involution: dual(dual(f)) structurally equal for a sample formula.
    const f = b.tensorF(a, b.parF(b.negAtom(1), b.botF()));
    const dd = b.dual(b.dual(f));
    try testing.expect(eqF(f, dd));
}

fn eqF(a: *const Formula, b2: *const Formula) bool {
    if (@as(std.meta.Tag(Formula), a.*) != @as(std.meta.Tag(Formula), b2.*)) return false;
    return switch (a.*) {
        .pos => |i| b2.pos == i,
        .negA => |i| b2.negA == i,
        .tensor => |p| eqF(p[0], b2.tensor[0]) and eqF(p[1], b2.tensor[1]),
        .par => |p| eqF(p[0], b2.par[0]) and eqF(p[1], b2.par[1]),
        .one, .bot => true,
    };
}
