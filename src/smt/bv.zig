//! Bit-vector SMT-lite: bit-blast simple BV formulas to CNF.

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
        const ta = self.term(a);
        const tb = self.term(b);
        std.debug.assert(ta.width == tb.width);
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
        const ta = self.term(a);
        const tb = self.term(b);
        std.debug.assert(ta.width == tb.width);
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
        const ta = self.term(a);
        const tb = self.term(b);
        std.debug.assert(ta.width == tb.width);
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
        const ta = self.term(a);
        const tb = self.term(b);
        std.debug.assert(ta.width == tb.width);
        var i: u8 = 0;
        while (i < ta.width) : (i += 1) {
            const xa = Lit.positive(Var.fromIndex(ta.bits[i]));
            const xb = Lit.positive(Var.fromIndex(tb.bits[i]));
            try self.cnf.addClause(&.{ xa.not(), xb });
            try self.cnf.addClause(&.{ xa, xb.not() });
        }
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
