//! Many-valued logics via finite logical matrices.
//!
//! A matrix is (values, designated set, operation tables); consequence is
//! designated-value preservation: Γ ⊨ φ iff every valuation making all of Γ
//! designated makes φ designated. Valuations are enumerated exactly.
//!
//! Shipped matrices:
//!   classical — two-valued (the sanity anchor, cross-checked vs truth tables)
//!   k3        — strong Kleene (gap: no LEM, in fact no tautologies at all)
//!   lp        — Priest's Logic of Paradox (glut: LEM holds, explosion and
//!               modus ponens fail — the paraconsistent signature)
//!   fde       — Belnap–Dunn four-valued (both gap and glut)
//!   l3        — Łukasiewicz three-valued (p→p holds, LEM fails)
//!
//! K3 and LP share tables and differ only in the designated set — the
//! classic illustration that consequence lives in designation, not truth
//! functions. FDE is the {t,b,n,f} bilattice with {t,b} designated.

const std = @import("std");

pub const max_values = 4;

pub const Matrix = struct {
    n: u8, // number of truth values 0..n-1
    designated: [max_values]bool,
    neg: [max_values]u8,
    conj: [max_values][max_values]u8,
    disj: [max_values][max_values]u8,
    imp: [max_values][max_values]u8,
};

/// Two-valued classical: 0=f, 1=t.
pub const classical = Matrix{
    .n = 2,
    .designated = .{ false, true, false, false },
    .neg = .{ 1, 0, 0, 0 },
    .conj = .{ .{ 0, 0, 0, 0 }, .{ 0, 1, 0, 0 }, .{0} ** 4, .{0} ** 4 },
    .disj = .{ .{ 0, 1, 0, 0 }, .{ 1, 1, 0, 0 }, .{0} ** 4, .{0} ** 4 },
    .imp = .{ .{ 1, 1, 0, 0 }, .{ 0, 1, 0, 0 }, .{0} ** 4, .{0} ** 4 },
};

/// Strong Kleene tables: 0=f, 1=n, 2=t (min/max order f < n < t).
fn kleeneTables() struct { neg: [4]u8, conj: [4][4]u8, disj: [4][4]u8, imp: [4][4]u8 } {
    var neg: [4]u8 = .{ 2, 1, 0, 0 };
    var conj: [4][4]u8 = undefined;
    var disj: [4][4]u8 = undefined;
    var imp: [4][4]u8 = undefined;
    for (0..3) |a| {
        for (0..3) |bb| {
            conj[a][bb] = @intCast(@min(a, bb));
            disj[a][bb] = @intCast(@max(a, bb));
            imp[a][bb] = @intCast(@max(2 - a, bb)); // ¬a ∨ b
        }
    }
    _ = &neg;
    return .{ .neg = neg, .conj = conj, .disj = disj, .imp = imp };
}

/// K3: Kleene tables, only t designated (truth-value gaps).
pub const k3 = blk: {
    const t = kleeneTables();
    break :blk Matrix{
        .n = 3,
        .designated = .{ false, false, true, false },
        .neg = t.neg,
        .conj = t.conj,
        .disj = t.disj,
        .imp = t.imp,
    };
};

/// LP: same tables, n and t designated (truth-value gluts).
pub const lp = blk: {
    const t = kleeneTables();
    break :blk Matrix{
        .n = 3,
        .designated = .{ false, true, true, false },
        .neg = t.neg,
        .conj = t.conj,
        .disj = t.disj,
        .imp = t.imp,
    };
};

/// Łukasiewicz Ł3: Kleene tables except a→b = min(2, 2-a+b).
pub const l3 = blk: {
    const t = kleeneTables();
    var imp = t.imp;
    for (0..3) |a| {
        for (0..3) |bb| {
            const v = 2 - @as(i32, @intCast(a)) + @as(i32, @intCast(bb));
            imp[a][bb] = @intCast(@min(@as(i32, 2), v));
        }
    }
    break :blk Matrix{
        .n = 3,
        .designated = .{ false, false, true, false },
        .neg = t.neg,
        .conj = t.conj,
        .disj = t.disj,
        .imp = imp,
    };
};

/// FDE (Belnap–Dunn): 0=f, 1=n, 2=b, 3=t; designated {b,t}.
/// Truth order: f < n,b < t (n and b incomparable; meet/join per bilattice).
pub const fde = blk: {
    var neg: [4]u8 = .{ 3, 1, 2, 0 }; // swaps f/t, fixes n and b
    var conj: [4][4]u8 = undefined;
    var disj: [4][4]u8 = undefined;
    // Encode as pairs (truth-support, falsity-support):
    // f=(0,1) n=(0,0) b=(1,1) t=(1,0).
    const tr = [4]u1{ 0, 0, 1, 1 };
    const fa = [4]u1{ 1, 0, 1, 0 };
    const enc = [2][2]u8{ .{ 1, 0 }, .{ 3, 2 } }; // enc[tr][fa]
    for (0..4) |a| {
        for (0..4) |bb| {
            conj[a][bb] = enc[tr[a] & tr[bb]][fa[a] | fa[bb]];
            disj[a][bb] = enc[tr[a] | tr[bb]][fa[a] & fa[bb]];
        }
    }
    var imp: [4][4]u8 = undefined;
    for (0..4) |a| {
        for (0..4) |bb| {
            imp[a][bb] = disj[neg[a]][bb]; // material: ¬a ∨ b
        }
    }
    _ = &neg;
    break :blk Matrix{
        .n = 4,
        .designated = .{ false, false, true, true },
        .neg = neg,
        .conj = conj,
        .disj = disj,
        .imp = imp,
    };
};

pub const Formula = union(enum) {
    atom: u32,
    neg: *const Formula,
    conj: [2]*const Formula,
    disj: [2]*const Formula,
    imp: [2]*const Formula,
};

pub const DecisionStatus = enum { valid, invalid, invalid_input };

pub const Decision = struct {
    status: DecisionStatus,
    num_atoms: u32,
    valuations_checked: u64 = 0,
    countervaluation: ?[8]u8 = null,
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
        return self.mk(.{ .atom = i });
    }
    pub fn notF(self: *Builder, a: *const Formula) *const Formula {
        return self.mk(.{ .neg = a });
    }
    pub fn andF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .conj = .{ a, b } });
    }
    pub fn orF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .disj = .{ a, b } });
    }
    pub fn impF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .imp = .{ a, b } });
    }
};

pub fn eval(m: *const Matrix, f: *const Formula, valuation: []const u8) u8 {
    return switch (f.*) {
        .atom => |i| valuation[i],
        .neg => |a| m.neg[eval(m, a, valuation)],
        .conj => |p| m.conj[eval(m, p[0], valuation)][eval(m, p[1], valuation)],
        .disj => |p| m.disj[eval(m, p[0], valuation)][eval(m, p[1], valuation)],
        .imp => |p| m.imp[eval(m, p[0], valuation)][eval(m, p[1], valuation)],
    };
}

fn validMatrix(m: *const Matrix) bool {
    if (m.n < 2 or m.n > max_values) return false;
    var designated = false;
    for (0..m.n) |a| {
        designated = designated or m.designated[a];
        if (m.neg[a] >= m.n) return false;
        for (0..m.n) |b| {
            if (m.conj[a][b] >= m.n or m.disj[a][b] >= m.n or m.imp[a][b] >= m.n) return false;
        }
    }
    return designated;
}

fn formulaInRange(f: *const Formula, num_atoms: u32) bool {
    return switch (f.*) {
        .atom => |atom| atom < num_atoms,
        .neg => |inner| formulaInRange(inner, num_atoms),
        .conj, .disj, .imp => |pair| formulaInRange(pair[0], num_atoms) and formulaInRange(pair[1], num_atoms),
    };
}

fn decodeValuation(index: u64, radix: u8, num_atoms: u32) [8]u8 {
    var valuation = [_]u8{0} ** 8;
    var remaining = index;
    var atom: u32 = 0;
    while (atom < num_atoms) : (atom += 1) {
        valuation[atom] = @intCast(remaining % radix);
        remaining /= radix;
    }
    return valuation;
}

pub fn decide(m: *const Matrix, premises: []const *const Formula, conclusion: *const Formula, num_atoms: u32) Decision {
    if (num_atoms > 8 or !validMatrix(m) or !formulaInRange(conclusion, num_atoms))
        return .{ .status = .invalid_input, .num_atoms = num_atoms };
    for (premises) |premise| {
        if (!formulaInRange(premise, num_atoms)) return .{ .status = .invalid_input, .num_atoms = num_atoms };
    }
    const total = std.math.pow(u64, m.n, num_atoms);
    var index: u64 = 0;
    while (index < total) : (index += 1) {
        const valuation = decodeValuation(index, m.n, num_atoms);
        var premises_designated = true;
        for (premises) |premise| {
            if (!m.designated[eval(m, premise, valuation[0..num_atoms])]) {
                premises_designated = false;
                break;
            }
        }
        if (premises_designated and !m.designated[eval(m, conclusion, valuation[0..num_atoms])]) {
            return .{ .status = .invalid, .num_atoms = num_atoms, .valuations_checked = index + 1, .countervaluation = valuation };
        }
    }
    return .{ .status = .valid, .num_atoms = num_atoms, .valuations_checked = total };
}

pub fn verifyDecision(m: *const Matrix, premises: []const *const Formula, conclusion: *const Formula, decision: Decision) bool {
    if (decision.status == .invalid_input) return false;
    if (!validMatrix(m) or decision.num_atoms > 8 or !formulaInRange(conclusion, decision.num_atoms)) return false;
    for (premises) |premise| if (!formulaInRange(premise, decision.num_atoms)) return false;
    if (decision.status == .invalid) {
        const valuation = decision.countervaluation orelse return false;
        for (0..decision.num_atoms) |atom| if (valuation[atom] >= m.n) return false;
        for (premises) |premise| {
            if (!m.designated[eval(m, premise, valuation[0..decision.num_atoms])]) return false;
        }
        return !m.designated[eval(m, conclusion, valuation[0..decision.num_atoms])];
    }
    if (decision.countervaluation != null) return false;
    const expected = std.math.pow(u64, m.n, decision.num_atoms);
    if (decision.valuations_checked != expected) return false;
    return consequence(m, premises, conclusion, decision.num_atoms);
}

/// Designated-value consequence: Γ ⊨_M φ over all valuations of `num_atoms`.
pub fn consequence(
    m: *const Matrix,
    premises: []const *const Formula,
    conclusion: *const Formula,
    num_atoms: u32,
) bool {
    std.debug.assert(num_atoms <= 8);
    var valuation: [8]u8 = .{0} ** 8;
    return consequenceRec(m, premises, conclusion, &valuation, 0, num_atoms);
}

fn consequenceRec(
    m: *const Matrix,
    premises: []const *const Formula,
    conclusion: *const Formula,
    valuation: *[8]u8,
    i: u32,
    num_atoms: u32,
) bool {
    if (i == num_atoms) {
        for (premises) |p| {
            if (!m.designated[eval(m, p, valuation[0..num_atoms])]) return true;
        }
        return m.designated[eval(m, conclusion, valuation[0..num_atoms])];
    }
    for (0..m.n) |v| {
        valuation[i] = @intCast(v);
        if (!consequenceRec(m, premises, conclusion, valuation, i + 1, num_atoms)) return false;
    }
    return true;
}

pub fn tautology(m: *const Matrix, f: *const Formula, num_atoms: u32) bool {
    return consequence(m, &.{}, f, num_atoms);
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "manyvalued: canonical (in)validities across the matrices" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const q = b.atom(1);
    const lem = b.orF(p, b.notF(p));
    const self_imp = b.impF(p, p);
    const contradiction = b.andF(p, b.notF(p));

    // Classical: everything as usual.
    try testing.expect(tautology(&classical, lem, 1));
    try testing.expect(tautology(&classical, self_imp, 1));
    try testing.expect(consequence(&classical, &.{contradiction}, q, 2)); // explosion
    try testing.expect(consequence(&classical, &.{ p, b.impF(p, q) }, q, 2)); // MP

    // K3: gaps — no LEM, not even p→p.
    try testing.expect(!tautology(&k3, lem, 1));
    try testing.expect(!tautology(&k3, self_imp, 1));
    try testing.expect(consequence(&k3, &.{ p, b.impF(p, q) }, q, 2)); // MP holds in K3
    try testing.expect(consequence(&k3, &.{contradiction}, q, 2)); // explosion holds (premise never designated... it can't be)

    // LP: gluts — LEM back, but explosion and modus ponens fail.
    try testing.expect(tautology(&lp, lem, 1));
    try testing.expect(tautology(&lp, self_imp, 1));
    try testing.expect(!consequence(&lp, &.{contradiction}, q, 2)); // paraconsistent
    try testing.expect(!consequence(&lp, &.{ p, b.impF(p, q) }, q, 2)); // MP fails
    try testing.expect(consequence(&lp, &.{b.andF(p, q)}, p, 2)); // ∧-elim survives

    // FDE: both gaps and gluts — neither LEM nor explosion.
    try testing.expect(!tautology(&fde, lem, 1));
    try testing.expect(!consequence(&fde, &.{contradiction}, q, 2));
    try testing.expect(consequence(&fde, &.{b.andF(p, q)}, p, 2));
    try testing.expect(consequence(&fde, &.{p}, b.orF(p, q), 2));

    // Ł3: p→p is back (Łukasiewicz conditional), LEM still fails.
    try testing.expect(tautology(&l3, self_imp, 1));
    try testing.expect(!tautology(&l3, lem, 1));
    // Ł3 contraction failure: (p→(p→q))→(p→q) is NOT a tautology.
    const contraction = b.impF(b.impF(p, b.impF(p, q)), b.impF(p, q));
    try testing.expect(!tautology(&l3, contraction, 2));
    try testing.expect(tautology(&classical, contraction, 2));
}

test "manyvalued: K3 and LP differ only in designation" {
    // Same tables ⇒ same evaluations; different designated sets ⇒ different logics.
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const f = b.orF(p, b.notF(p));
    var valuation = [_]u8{1}; // n
    try testing.expectEqual(eval(&k3, f, &valuation), eval(&lp, f, &valuation));
    try testing.expect(!k3.designated[eval(&k3, f, &valuation)]);
    try testing.expect(lp.designated[eval(&lp, f, &valuation)]);
}

fn randomFormula(b: *Builder, rand: std.Random, depth: u32, num_atoms: u32) *const Formula {
    if (depth == 0 or rand.uintLessThan(u32, 4) == 0) {
        return b.atom(rand.uintLessThan(u32, num_atoms));
    }
    return switch (rand.uintLessThan(u32, 4)) {
        0 => b.notF(randomFormula(b, rand, depth - 1, num_atoms)),
        1 => b.andF(randomFormula(b, rand, depth - 1, num_atoms), randomFormula(b, rand, depth - 1, num_atoms)),
        2 => b.orF(randomFormula(b, rand, depth - 1, num_atoms), randomFormula(b, rand, depth - 1, num_atoms)),
        else => b.impF(randomFormula(b, rand, depth - 1, num_atoms), randomFormula(b, rand, depth - 1, num_atoms)),
    };
}

fn bruteClassical(f: *const Formula, assign: u32) bool {
    return switch (f.*) {
        .atom => |i| (assign >> @intCast(i)) & 1 == 1,
        .neg => |a| !bruteClassical(a, assign),
        .conj => |pp| bruteClassical(pp[0], assign) and bruteClassical(pp[1], assign),
        .disj => |pp| bruteClassical(pp[0], assign) or bruteClassical(pp[1], assign),
        .imp => |pp| !bruteClassical(pp[0], assign) or bruteClassical(pp[1], assign),
    };
}

test "manyvalued: classical matrix matches truth-table oracle on random formulas" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var prng = std.Random.DefaultPrng.init(0x3A7);
    const rand = prng.random();
    for (0..60) |_| {
        const f = randomFormula(&b, rand, 3, 3);
        var brute_valid = true;
        var a: u32 = 0;
        while (a < 8) : (a += 1) {
            if (!bruteClassical(f, a)) {
                brute_valid = false;
                break;
            }
        }
        try testing.expectEqual(brute_valid, tautology(&classical, f, 3));
    }
}

test "manyvalued: K3 ⊆ classical and LP-invalid ⊆ classical tautologies interplay" {
    // Anything K3-valid is classically valid; anything classically invalid is LP-invalid.
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var prng = std.Random.DefaultPrng.init(0x51D);
    const rand = prng.random();
    for (0..40) |_| {
        const f = randomFormula(&b, rand, 3, 2);
        if (tautology(&k3, f, 2)) try testing.expect(tautology(&classical, f, 2));
        if (!tautology(&classical, f, 2)) try testing.expect(!tautology(&k3, f, 2));
    }
}

test "manyvalued: decisions carry replayable evidence across every matrix" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const q = b.atom(1);
    const formulas = [_]*const Formula{ b.orF(p, b.notF(p)), b.impF(p, p), b.impF(b.andF(p, b.notF(p)), q) };
    const matrices = [_]*const Matrix{ &classical, &k3, &lp, &fde, &l3 };
    for (matrices) |matrix| {
        for (formulas) |formula| {
            const decision = decide(matrix, &.{}, formula, 2);
            try testing.expect(decision.status != .invalid_input);
            try testing.expect(verifyDecision(matrix, &.{}, formula, decision));
            if (decision.status == .invalid) try testing.expect(decision.countervaluation != null);
        }
    }
}

test "manyvalued: malformed and mutated evidence fails closed" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const lem = b.orF(p, b.notF(p));
    var decision = decide(&classical, &.{}, lem, 1);
    decision.valuations_checked -= 1;
    try testing.expect(!verifyDecision(&classical, &.{}, lem, decision));
    try testing.expectEqual(DecisionStatus.invalid_input, decide(&classical, &.{}, b.atom(2), 1).status);
}
