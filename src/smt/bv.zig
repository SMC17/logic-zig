//! Bit-vector SMT-lite: bit-blast simple BV formulas to CNF.
//!
//! Width-mismatched binary ops return `error.WidthMismatch` (no silent truncate).
//! Not a full BV solver (no shifts/extract/sign-ext/div); ground bit-blast only.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const BvId = enum(u32) {
    _,
    pub fn index(self: BvId) u32 {
        return @intFromEnum(self);
    }
};

pub const BvError = error{
    WidthMismatch,
};

const BvTerm = struct {
    width: u8,
    bits: []u32,
};

pub const BvWorld = struct {
    allocator: std.mem.Allocator,
    cnf: Cnf,
    terms: std.ArrayList(BvTerm) = .empty,
    next_var: u32 = 0,

    pub fn init(allocator: std.mem.Allocator) BvWorld {
        return .{ .allocator = allocator, .cnf = Cnf.init(allocator) };
    }

    pub fn deinit(self: *BvWorld) void {
        for (self.terms.items) |t| self.allocator.free(t.bits);
        self.terms.deinit(self.allocator);
        self.cnf.deinit();
        self.* = undefined;
    }

    fn freshBits(self: *BvWorld, width: u8) ![]u32 {
        const bits = try self.allocator.alloc(u32, width);
        var i: u8 = 0;
        while (i < width) : (i += 1) {
            bits[i] = self.next_var;
            self.next_var += 1;
        }
        self.cnf.ensureVars(self.next_var);
        return bits;
    }

    fn pushTerm(self: *BvWorld, width: u8, bits: []u32) !BvId {
        const id: BvId = @enumFromInt(self.terms.items.len);
        try self.terms.append(self.allocator, .{ .width = width, .bits = bits });
        return id;
    }

    fn requireSameWidth(self: *BvWorld, a: BvId, b: BvId) BvError!void {
        const ta = self.term(a);
        const tb = self.term(b);
        if (ta.width != tb.width) return error.WidthMismatch;
    }

    pub fn widthOf(self: *BvWorld, id: BvId) u8 {
        return self.term(id).width;
    }

    pub fn mkVar(self: *BvWorld, width: u8) !BvId {
        return try self.pushTerm(width, try self.freshBits(width));
    }

    pub fn mkConst(self: *BvWorld, width: u8, value: u64) !BvId {
        const bits = try self.freshBits(width);
        var i: u8 = 0;
        while (i < width) : (i += 1) {
            const lit = Lit.positive(Var.fromIndex(bits[i]));
            if (((value >> @as(u6, @intCast(i))) & 1) == 1) try self.cnf.addClause(&.{lit}) else try self.cnf.addClause(&.{lit.not()});
        }
        return try self.pushTerm(width, bits);
    }

    fn term(self: *BvWorld, id: BvId) *BvTerm {
        return &self.terms.items[id.index()];
    }

    pub fn mkNot(self: *BvWorld, a: BvId) !BvId {
        const ta = self.term(a);
        const bits = try self.freshBits(ta.width);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const y = Lit.positive(Var.fromIndex(bits[i]));
            const x = Lit.positive(Var.fromIndex(ta.bits[i]));
            try self.cnf.addClause(&.{ y.not(), x.not() });
            try self.cnf.addClause(&.{ y, x });
        }
        return try self.pushTerm(ta.width, bits);
    }

    pub fn mkAnd(self: *BvWorld, a: BvId, b: BvId) !BvId {
        try self.requireSameWidth(a, b);
        const ta = self.term(a);
        const tb = self.term(b);
        const bits = try self.freshBits(ta.width);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const y = Lit.positive(Var.fromIndex(bits[i]));
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            try self.cnf.addClause(&.{ y.not(), xa });
            try self.cnf.addClause(&.{ y.not(), xb });
            try self.cnf.addClause(&.{ y, xa.not(), xb.not() });
        }
        return try self.pushTerm(ta.width, bits);
    }

    pub fn mkXor(self: *BvWorld, a: BvId, b: BvId) !BvId {
        try self.requireSameWidth(a, b);
        const ta = self.term(a);
        const tb = self.term(b);
        const bits = try self.freshBits(ta.width);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const y = Lit.positive(Var.fromIndex(bits[i]));
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            try self.cnf.addClause(&.{ y.not(), xa, xb });
            try self.cnf.addClause(&.{ y.not(), xa.not(), xb.not() });
            try self.cnf.addClause(&.{ y, xa.not(), xb });
            try self.cnf.addClause(&.{ y, xa, xb.not() });
        }
        return try self.pushTerm(ta.width, bits);
    }

    fn encodeXor(self: *BvWorld, y: Lit, a: Lit, b: Lit) !void {
        try self.cnf.addClause(&.{ y.not(), a, b });
        try self.cnf.addClause(&.{ y.not(), a.not(), b.not() });
        try self.cnf.addClause(&.{ y, a.not(), b });
        try self.cnf.addClause(&.{ y, a, b.not() });
    }

    fn encodeAnd(self: *BvWorld, y: Lit, a: Lit, b: Lit) !void {
        try self.cnf.addClause(&.{ y.not(), a });
        try self.cnf.addClause(&.{ y.not(), b });
        try self.cnf.addClause(&.{ y, a.not(), b.not() });
    }

    /// Ripple-carry add (mod 2^w).
    pub fn mkAdd(self: *BvWorld, a: BvId, b: BvId) !BvId {
        try self.requireSameWidth(a, b);
        const ta = self.term(a);
        const tb = self.term(b);
        const bits = try self.freshBits(ta.width);
        var cin: ?Lit = null;
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            const sum = Lit.positive(Var.fromIndex(bits[i]));
            if (cin) |c| {
                // s = a ⊕ b ⊕ c
                const ab_bits = try self.freshBits(1);
                defer self.allocator.free(ab_bits);
                const ab = Lit.positive(Var.fromIndex(ab_bits[0]));
                try self.encodeXor(ab, xa, xb);
                try self.encodeXor(sum, ab, c);
                // cout = (a∧b) ∨ (c∧(a⊕b))
                const ab_and_bits = try self.freshBits(1);
                defer self.allocator.free(ab_and_bits);
                const ab_and = Lit.positive(Var.fromIndex(ab_and_bits[0]));
                try self.encodeAnd(ab_and, xa, xb);
                const cab_bits = try self.freshBits(1);
                defer self.allocator.free(cab_bits);
                const cab = Lit.positive(Var.fromIndex(cab_bits[0]));
                try self.encodeAnd(cab, c, ab);
                const cout_bits = try self.freshBits(1);
                const cout = Lit.positive(Var.fromIndex(cout_bits[0]));
                try self.cnf.addClause(&.{ cout.not(), ab_and, cab });
                try self.cnf.addClause(&.{ ab_and.not(), cout });
                try self.cnf.addClause(&.{ cab.not(), cout });
                cin = cout;
                // aux bit arrays only hold var indices already tracked in next_var; free the slice shells
                self.allocator.free(cout_bits);
            } else {
                try self.encodeXor(sum, xa, xb);
                const cb = try self.freshBits(1);
                const cout = Lit.positive(Var.fromIndex(cb[0]));
                try self.encodeAnd(cout, xa, xb);
                cin = cout;
                self.allocator.free(cb);
            }
        }
        return try self.pushTerm(ta.width, bits);
    }

    pub fn assertEq(self: *BvWorld, a: BvId, b: BvId) !void {
        try self.requireSameWidth(a, b);
        const ta = self.term(a);
        const tb = self.term(b);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            try self.cnf.addClause(&.{ xa.not(), xb });
            try self.cnf.addClause(&.{ xa, xb.not() });
        }
    }

    /// Assert a ≠ b by requiring at least one bit differ (same width).
    pub fn assertNe(self: *BvWorld, a: BvId, b: BvId) !void {
        try self.requireSameWidth(a, b);
        const ta = self.term(a);
        const tb = self.term(b);
        // ∨_i (a_i XOR b_i)  encoded as a clause over pairwise xor aux, or
        // simpler: for each bit, (a≠b at i) is (a∨b)∧(¬a∨¬b); big OR of differences.
        // CNF: introduce d_i ↔ a_i XOR b_i, then (d0 ∨ d1 ∨ …).
        var diff_lits: std.ArrayList(Lit) = .empty;
        defer diff_lits.deinit(self.allocator);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            const db = try self.freshBits(1);
            defer self.allocator.free(db);
            const d = Lit.positive(Var.fromIndex(db[0]));
            try self.encodeXor(d, xa, xb);
            try diff_lits.append(self.allocator, d);
        }
        try self.cnf.addClause(diff_lits.items);
    }

    pub fn checkSat(self: *BvWorld) !solver_mod.SolveStatus {
        const r = try solver_mod.solveCnf(self.allocator, &self.cnf, .{ .complete_model = true });
        defer if (r.model) |m| self.allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        return r.status;
    }
};

// ── unit tests ───────────────────────────────────────────────────────

test "bv add 2+2=4" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 2);
    const b = try w.mkConst(4, 2);
    const s = try w.mkAdd(a, b);
    const four = try w.mkConst(4, 4);
    try w.assertEq(s, four);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv unsat 1=0" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 1);
    const z = try w.mkConst(4, 0);
    try w.assertEq(a, z);
    try std.testing.expect((try w.checkSat()) == .unsat);
}

test "bv and" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 0b1100);
    const b = try w.mkConst(4, 0b1010);
    const c = try w.mkAnd(a, b);
    const expect = try w.mkConst(4, 0b1000);
    try w.assertEq(c, expect);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv xor" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 0b1100);
    const b = try w.mkConst(4, 0b1010);
    const c = try w.mkXor(a, b);
    const expect = try w.mkConst(4, 0b0110);
    try w.assertEq(c, expect);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv not" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 0b1010);
    const n = try w.mkNot(a);
    const expect = try w.mkConst(4, 0b0101);
    try w.assertEq(n, expect);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv var equality constraint sat" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const x = try w.mkVar(8);
    const y = try w.mkVar(8);
    try w.assertEq(x, y);
    // x = y free: sat
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv var equality with const" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const x = try w.mkVar(4);
    const c = try w.mkConst(4, 7);
    try w.assertEq(x, c);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv assertNe sat when free" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const x = try w.mkVar(4);
    const y = try w.mkVar(4);
    try w.assertNe(x, y);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv assertNe unsat when forced equal" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 5);
    const b = try w.mkConst(4, 5);
    try w.assertNe(a, b);
    try std.testing.expect((try w.checkSat()) == .unsat);
}

test "bv assertEq then Ne unsat" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const x = try w.mkVar(3);
    const y = try w.mkVar(3);
    try w.assertEq(x, y);
    try w.assertNe(x, y);
    try std.testing.expect((try w.checkSat()) == .unsat);
}

test "bv width mismatch assertEq" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 1);
    const b = try w.mkConst(8, 1);
    try std.testing.expectError(error.WidthMismatch, w.assertEq(a, b));
}

test "bv width mismatch assertNe" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkVar(2);
    const b = try w.mkVar(3);
    try std.testing.expectError(error.WidthMismatch, w.assertNe(a, b));
}

test "bv width mismatch mkAnd" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkVar(4);
    const b = try w.mkVar(8);
    try std.testing.expectError(error.WidthMismatch, w.mkAnd(a, b));
}

test "bv width mismatch mkXor" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(1, 1);
    const b = try w.mkConst(2, 1);
    try std.testing.expectError(error.WidthMismatch, w.mkXor(a, b));
}

test "bv width mismatch mkAdd" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 1);
    const b = try w.mkConst(8, 1);
    try std.testing.expectError(error.WidthMismatch, w.mkAdd(a, b));
}

test "bv add wrap 8-bit 255+1=0" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(8, 255);
    const b = try w.mkConst(8, 1);
    const s = try w.mkAdd(a, b);
    const z = try w.mkConst(8, 0);
    try w.assertEq(s, z);
    try std.testing.expect((try w.checkSat()) == .sat);
}

test "bv add wrong sum unsat" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkConst(4, 3);
    const b = try w.mkConst(4, 4);
    const s = try w.mkAdd(a, b);
    const wrong = try w.mkConst(4, 0);
    try w.assertEq(s, wrong);
    try std.testing.expect((try w.checkSat()) == .unsat);
}

test "bv widthOf" {
    var w = BvWorld.init(std.testing.allocator);
    defer w.deinit();
    const a = try w.mkVar(13);
    try std.testing.expect(w.widthOf(a) == 13);
}
