//! Packed propositional literals.
//!
//! Encoding: `lit = (var << 1) | sign` where sign=1 means negated.
//! Variables are 0-indexed internally; DIMACS uses 1-indexed ints.

const std = @import("std");

pub const Var = enum(u32) {
    _,

    pub fn fromIndex(i: u32) Var {
        return @enumFromInt(i);
    }

    pub fn index(self: Var) u32 {
        return @intFromEnum(self);
    }

    /// DIMACS variable number (1-based).
    pub fn dimacs(self: Var) i32 {
        return @intCast(self.index() + 1);
    }

    pub fn fromDimacs(d: i32) Var {
        std.debug.assert(d > 0);
        return fromIndex(@intCast(d - 1));
    }
};

pub const Lit = enum(u32) {
    _,

    pub fn make(v: Var, negated: bool) Lit {
        return @enumFromInt((v.index() << 1) | @intFromBool(negated));
    }

    pub fn positive(v: Var) Lit {
        return make(v, false);
    }

    pub fn negative(v: Var) Lit {
        return make(v, true);
    }

    /// From a signed DIMACS integer (nonzero).
    pub fn fromDimacs(d: i32) Lit {
        std.debug.assert(d != 0);
        const neg = d < 0;
        const abs: u32 = @intCast(if (d < 0) -d else d);
        return make(Var.fromIndex(abs - 1), neg);
    }

    pub fn toDimacs(self: Lit) i32 {
        const v: i32 = @intCast(self.variable().index() + 1);
        return if (self.isNeg()) -v else v;
    }

    pub fn variable(self: Lit) Var {
        return Var.fromIndex(@intFromEnum(self) >> 1);
    }

    pub fn isNeg(self: Lit) bool {
        return (@intFromEnum(self) & 1) == 1;
    }

    pub fn not(self: Lit) Lit {
        return @enumFromInt(@intFromEnum(self) ^ 1);
    }

    /// Index into watch arrays of length 2*num_vars.
    pub fn watchIndex(self: Lit) u32 {
        return @intFromEnum(self);
    }

    pub fn format(self: Lit, writer: *std.io.Writer) !void {
        if (self.isNeg()) try writer.writeByte('-');
        try writer.print("x{d}", .{self.variable().index()});
    }
};

pub const Value = enum(u8) {
    undef = 0,
    true_ = 1,
    false_ = 2,

    pub fn fromBool(b: bool) Value {
        return if (b) .true_ else .false_;
    }

    pub fn toBool(self: Value) ?bool {
        return switch (self) {
            .undef => null,
            .true_ => true,
            .false_ => false,
        };
    }

    pub fn isTrue(self: Value) bool {
        return self == .true_;
    }

    pub fn isFalse(self: Value) bool {
        return self == .false_;
    }

    pub fn isUndef(self: Value) bool {
        return self == .undef;
    }
};

/// Evaluate a literal under a variable assignment array indexed by Var.index().
pub fn evalLit(lit: Lit, assign: []const Value) Value {
    const v = assign[lit.variable().index()];
    if (v == .undef) return .undef;
    if (lit.isNeg()) {
        return if (v == .true_) .false_ else .true_;
    }
    return v;
}

test "lit packing roundtrip" {
    const v = Var.fromIndex(3);
    const p = Lit.positive(v);
    const n = Lit.negative(v);
    try std.testing.expect(p.variable().index() == 3);
    try std.testing.expect(!p.isNeg());
    try std.testing.expect(n.isNeg());
    try std.testing.expect(p.not().isNeg());
    try std.testing.expect(n.not().watchIndex() == p.watchIndex());
    try std.testing.expect(Lit.fromDimacs(-4).toDimacs() == -4);
    try std.testing.expect(Lit.fromDimacs(4).toDimacs() == 4);
}

test "evalLit" {
    var assign = [_]Value{ .undef, .true_, .false_ };
    const x0 = Lit.positive(Var.fromIndex(0));
    const x1n = Lit.negative(Var.fromIndex(1));
    try std.testing.expect(evalLit(x0, &assign) == .undef);
    try std.testing.expect(evalLit(x1n, &assign) == .false_); // ~true = false
    try std.testing.expect(evalLit(Lit.positive(Var.fromIndex(2)), &assign) == .false_);
}
