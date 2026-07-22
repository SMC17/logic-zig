//! Intuitionistic propositional logic — G4ip decision procedure.
//!
//! Dyckhoff's contraction-free sequent calculus (LJT/G4ip) decides
//! intuitionistic validity without loop checking: the left-implication rule
//! is split by the shape of the antecedent, and every rule application
//! strictly decreases a multiset measure.
//!
//!   axioms      Γ,A ⊢ A      Γ,⊥ ⊢ G
//!   R∧ R∨ R→    as usual (R→ moves the antecedent left)
//!   L∧          Γ,A,B ⊢ G          from Γ,A∧B ⊢ G
//!   L∨          both branches
//!   L→ (atom)   Γ,p,B ⊢ G          from Γ,p,p→B ⊢ G
//!   L→ (∧)      Γ,C→(D→B) ⊢ G      from Γ,(C∧D)→B ⊢ G
//!   L→ (∨)      Γ,C→B,D→B ⊢ G      from Γ,(C∨D)→B ⊢ G
//!   L→ (→)      Γ,D→B ⊢ C→D  and  Γ,B ⊢ G   from Γ,(C→D)→B ⊢ G
//!   L→ (⊥)      drop (⊥→B is ⊤)
//!
//! Contexts are immutable slices; every rule builds a fresh context, so
//! backtracking can never corrupt the multiset. Negation is sugar:
//! ¬A ≡ A→⊥. Canon: Peirce and excluded middle unprovable, their double
//! negations provable, plus a randomized Glivenko cross-check against a
//! classical truth-table oracle.

const std = @import("std");

pub const Formula = union(enum) {
    atom: u32,
    ff, // ⊥
    and_: [2]*const Formula,
    or_: [2]*const Formula,
    imp: [2]*const Formula,
};

/// Arena-backed formula builder.
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
        return self.mk(.{ .atom = i });
    }
    pub fn bot(self: *Builder) *const Formula {
        return self.mk(.ff);
    }
    pub fn andF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .and_ = .{ a, b } });
    }
    pub fn orF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .or_ = .{ a, b } });
    }
    pub fn impF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .imp = .{ a, b } });
    }
    pub fn notF(self: *Builder, a: *const Formula) *const Formula {
        return self.impF(a, self.bot());
    }
};

fn eqF(a: *const Formula, b: *const Formula) bool {
    if (a == b) return true;
    if (@as(std.meta.Tag(Formula), a.*) != @as(std.meta.Tag(Formula), b.*)) return false;
    return switch (a.*) {
        .atom => |x| b.atom == x,
        .ff => true,
        .and_ => |p| eqF(p[0], b.and_[0]) and eqF(p[1], b.and_[1]),
        .or_ => |p| eqF(p[0], b.or_[0]) and eqF(p[1], b.or_[1]),
        .imp => |p| eqF(p[0], b.imp[0]) and eqF(p[1], b.imp[1]),
    };
}

const Ctx = []const *const Formula;

fn ctxHasAtom(ctx: Ctx, i: u32) bool {
    for (ctx) |f| {
        switch (f.*) {
            .atom => |x| if (x == i) return true,
            else => {},
        }
    }
    return false;
}

/// New context = ctx without index `drop` (when non-null), plus `extra`.
fn replaced(
    allocator: std.mem.Allocator,
    ctx: Ctx,
    drop: ?usize,
    extra: []const *const Formula,
) ![]*const Formula {
    const keep = if (drop == null) ctx.len else ctx.len - 1;
    const out = try allocator.alloc(*const Formula, keep + extra.len);
    var k: usize = 0;
    for (ctx, 0..) |f, i| {
        if (drop != null and i == drop.?) continue;
        out[k] = f;
        k += 1;
    }
    for (extra) |f| {
        out[k] = f;
        k += 1;
    }
    return out;
}

fn proveSeq(allocator: std.mem.Allocator, b: *Builder, ctx: Ctx, goal: *const Formula) error{OutOfMemory}!bool {
    // Axioms and ⊥ on the left.
    for (ctx) |f| {
        if (f.* == .ff) return true;
        if (eqF(f, goal)) return true;
    }
    // Invertible right rules.
    switch (goal.*) {
        .and_ => |p| {
            if (!try proveSeq(allocator, b, ctx, p[0])) return false;
            return proveSeq(allocator, b, ctx, p[1]);
        },
        .imp => |p| {
            const c = try replaced(allocator, ctx, null, &.{p[0]});
            defer allocator.free(c);
            return proveSeq(allocator, b, c, p[1]);
        },
        else => {},
    }
    // Invertible left rules: apply the first applicable one.
    for (ctx, 0..) |f, i| {
        switch (f.*) {
            .and_ => |p| {
                const c = try replaced(allocator, ctx, i, &.{ p[0], p[1] });
                defer allocator.free(c);
                return proveSeq(allocator, b, c, goal);
            },
            .or_ => |p| {
                {
                    const c = try replaced(allocator, ctx, i, &.{p[0]});
                    defer allocator.free(c);
                    if (!try proveSeq(allocator, b, c, goal)) return false;
                }
                const c = try replaced(allocator, ctx, i, &.{p[1]});
                defer allocator.free(c);
                return proveSeq(allocator, b, c, goal);
            },
            .imp => |p| switch (p[0].*) {
                .ff => {
                    const c = try replaced(allocator, ctx, i, &.{});
                    defer allocator.free(c);
                    return proveSeq(allocator, b, c, goal);
                },
                .atom => |x| {
                    if (ctxHasAtom(ctx, x)) {
                        const c = try replaced(allocator, ctx, i, &.{p[1]});
                        defer allocator.free(c);
                        return proveSeq(allocator, b, c, goal);
                    }
                },
                .and_ => |q| {
                    const c = try replaced(allocator, ctx, i, &.{b.impF(q[0], b.impF(q[1], p[1]))});
                    defer allocator.free(c);
                    return proveSeq(allocator, b, c, goal);
                },
                .or_ => |q| {
                    const c = try replaced(allocator, ctx, i, &.{ b.impF(q[0], p[1]), b.impF(q[1], p[1]) });
                    defer allocator.free(c);
                    return proveSeq(allocator, b, c, goal);
                },
                .imp => {},
            },
            else => {},
        }
    }
    // Non-invertible choices: R∨ branches, then each L→(→) candidate.
    switch (goal.*) {
        .or_ => |p| {
            if (try proveSeq(allocator, b, ctx, p[0])) return true;
            if (try proveSeq(allocator, b, ctx, p[1])) return true;
        },
        else => {},
    }
    for (ctx, 0..) |f, i| {
        switch (f.*) {
            .imp => |p| switch (p[0].*) {
                .imp => |q| {
                    // Γ,(C→D)→B ⊢ G  ⇐  Γ,D→B ⊢ C→D  and  Γ,B ⊢ G
                    const c1 = try replaced(allocator, ctx, i, &.{b.impF(q[1], p[1])});
                    defer allocator.free(c1);
                    if (try proveSeq(allocator, b, c1, p[0])) {
                        const c2 = try replaced(allocator, ctx, i, &.{p[1]});
                        defer allocator.free(c2);
                        if (try proveSeq(allocator, b, c2, goal)) return true;
                    }
                },
                else => {},
            },
            else => {},
        }
    }
    return false;
}

/// Is the formula intuitionistically provable (⊢ f in G4ip)?
pub fn provable(allocator: std.mem.Allocator, b: *Builder, f: *const Formula) !bool {
    return proveSeq(allocator, b, &.{}, f);
}

/// Classical truth-table validity (test oracle and Glivenko partner).
pub fn classicallyValid(f: *const Formula, num_atoms: u32) bool {
    const total: u32 = @as(u32, 1) << @intCast(num_atoms);
    var a: u32 = 0;
    while (a < total) : (a += 1) {
        if (!evalClassical(f, a)) return false;
    }
    return true;
}

fn evalClassical(f: *const Formula, assign: u32) bool {
    return switch (f.*) {
        .atom => |i| (assign >> @intCast(i)) & 1 == 1,
        .ff => false,
        .and_ => |p| evalClassical(p[0], assign) and evalClassical(p[1], assign),
        .or_ => |p| evalClassical(p[0], assign) or evalClassical(p[1], assign),
        .imp => |p| !evalClassical(p[0], assign) or evalClassical(p[1], assign),
    };
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "g4ip: constructive canon" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const q = b.atom(1);

    // ⊢ p→p
    try testing.expect(try provable(testing.allocator, &b, b.impF(p, p)));
    // ⊢ p→(q→p)
    try testing.expect(try provable(testing.allocator, &b, b.impF(p, b.impF(q, p))));
    // ⊬ p∨¬p
    try testing.expect(!try provable(testing.allocator, &b, b.orF(p, b.notF(p))));
    // ⊢ ¬¬(p∨¬p)
    try testing.expect(try provable(testing.allocator, &b, b.notF(b.notF(b.orF(p, b.notF(p))))));
    // ⊬ ¬¬p→p
    try testing.expect(!try provable(testing.allocator, &b, b.impF(b.notF(b.notF(p)), p)));
    // ⊢ p→¬¬p
    try testing.expect(try provable(testing.allocator, &b, b.impF(p, b.notF(b.notF(p)))));
    // Peirce ⊬ ((p→q)→p)→p, but ⊢ ¬¬Peirce
    const peirce = b.impF(b.impF(b.impF(p, q), p), p);
    try testing.expect(!try provable(testing.allocator, &b, peirce));
    try testing.expect(try provable(testing.allocator, &b, b.notF(b.notF(peirce))));
    // ⊢ ¬¬(¬¬p→p) (Glivenko on double-negation elimination)
    try testing.expect(try provable(testing.allocator, &b, b.notF(b.notF(b.impF(b.notF(b.notF(p)), p)))));
    // Ex falso: ⊢ ⊥→p
    try testing.expect(try provable(testing.allocator, &b, b.impF(b.bot(), p)));
    // ⊢ (p∧q)→(q∧p)
    try testing.expect(try provable(testing.allocator, &b, b.impF(b.andF(p, q), b.andF(q, p))));
}

fn randomFormula(b: *Builder, rand: std.Random, depth: u32, num_atoms: u32) *const Formula {
    if (depth == 0 or rand.uintLessThan(u32, 4) == 0) {
        if (rand.uintLessThan(u32, 8) == 0) return b.bot();
        return b.atom(rand.uintLessThan(u32, num_atoms));
    }
    const l = randomFormula(b, rand, depth - 1, num_atoms);
    const r = randomFormula(b, rand, depth - 1, num_atoms);
    return switch (rand.uintLessThan(u32, 3)) {
        0 => b.andF(l, r),
        1 => b.orF(l, r),
        else => b.impF(l, r),
    };
}

test "g4ip: soundness + Glivenko vs classical oracle on random formulas" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var prng = std.Random.DefaultPrng.init(0x64117);
    const rand = prng.random();
    var glivenko_checked: u32 = 0;
    for (0..80) |_| {
        const f = randomFormula(&b, rand, 3, 3);
        const cls = classicallyValid(f, 3);
        const int = try provable(testing.allocator, &b, f);
        // Soundness: intuitionistically provable ⇒ classically valid.
        if (int) try testing.expect(cls);
        // Glivenko: classically valid ⇔ ¬¬f provable.
        const nn = try provable(testing.allocator, &b, b.notF(b.notF(f)));
        try testing.expectEqual(cls, nn);
        glivenko_checked += 1;
    }
    try testing.expectEqual(@as(u32, 80), glivenko_checked);
}
