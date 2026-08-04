//! Paraconsistent logic — Logic of Paradox (LP) / Belnap-Dunn four-valued.
//!
//! Classical explosion (ex contradictione quodlibet) fails: from A ∧ ¬A one
//! cannot derive arbitrary B. Truth values:
//!
//!   Belnap-Dunn FOUR:
//!     T  = true only
//!     F  = false only
//!     B  = both (glut / paradoxical)
//!     N  = neither (gap)
//!
//! LP is the {T,B}-designated fragment (truth-preserving under gluts).
//! Connectives use lattice meet/join on the knowledge and truth orders.
//!
//! Fragment: evaluator + designated-sat check. Not a full tableau prover.

const std = @import("std");

pub const Four = enum {
    /// True only.
    t,
    /// False only.
    f,
    /// Both true and false (glut).
    b,
    /// Neither (gap).
    n,

    pub fn isDesignatedLP(self: Four) bool {
        return self == .t or self == .b;
    }

    pub fn isDesignatedClassical(self: Four) bool {
        return self == .t;
    }
};

/// Truth order: F ≤ N,B ≤ T  (approx) — use meet/join tables from Dunn.
pub fn neg(v: Four) Four {
    return switch (v) {
        .t => .f,
        .f => .t,
        .b => .b,
        .n => .n,
    };
}

pub fn band(a: Four, b: Four) Four {
    // Lattice meet on approximation lattice F ≤ {N,B} ≤ T is wrong for Dunn;
    // use the standard Belnap tables:
    // AND is meet on the truth lattice: F < {B,N} < T with B incomparable N,
    // implemented via case analysis.
    return switch (a) {
        .f => .f,
        .t => b,
        .b => switch (b) {
            .f => .f,
            .t => .b,
            .b => .b,
            .n => .f, // B ∧ N = F in standard Belnap
        },
        .n => switch (b) {
            .f => .f,
            .t => .n,
            .b => .f,
            .n => .n,
        },
    };
}

pub fn bor(a: Four, b: Four) Four {
    return switch (a) {
        .t => .t,
        .f => b,
        .b => switch (b) {
            .t => .t,
            .f => .b,
            .b => .b,
            .n => .t, // B ∨ N = T
        },
        .n => switch (b) {
            .t => .t,
            .f => .n,
            .b => .t,
            .n => .n,
        },
    };
}

pub fn implies(a: Four, b: Four) Four {
    // Material: ¬a ∨ b
    return bor(neg(a), b);
}

pub const Formula = union(enum) {
    const_: Four,
    var_: u32,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    implies: struct { l: *Formula, r: *Formula },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*Formula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn f(self: *Arena, v: Formula) !*Formula {
        const p = try self.allocator.create(Formula);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

pub fn eval(phi: *const Formula, assign: []const Four) Four {
    return switch (phi.*) {
        .const_ => |c| c,
        .var_ => |i| assign[i],
        .not => |n| neg(eval(n, assign)),
        .and_ => |a| band(eval(a.l, assign), eval(a.r, assign)),
        .or_ => |a| bor(eval(a.l, assign), eval(a.r, assign)),
        .implies => |a| implies(eval(a.l, assign), eval(a.r, assign)),
    };
}

/// LP-entailment under a fixed assignment: conclusion designated whenever
/// all premises are. Explosion fails when premise is B.
pub fn lpDesignated(phi: *const Formula, assign: []const Four) bool {
    return eval(phi, assign).isDesignatedLP();
}

/// Does A ∧ ¬A entail B under LP? Only if B is designated whenever A is B or T.
/// Classic counterexample: A=B (both), B=F (false only) → premise designated, conclusion not.
pub fn explosionFailsExample() bool {
    // A = B (glut), formula A ∧ ¬A evaluates to B (designated in LP)
    // Target atom C = F → not designated
    // So LP does not validate explosion.
    const a_val: Four = .b;
    const c_val: Four = .f;
    const conj = band(a_val, neg(a_val)); // B ∧ B = B
    return conj.isDesignatedLP() and !c_val.isDesignatedLP();
}

test "negation of both is both" {
    try std.testing.expect(neg(.b) == .b);
    try std.testing.expect(neg(.n) == .n);
    try std.testing.expect(neg(.t) == .f);
}

test "LP designates glut" {
    try std.testing.expect(Four.b.isDesignatedLP());
    try std.testing.expect(!Four.f.isDesignatedLP());
    try std.testing.expect(!Four.n.isDesignatedLP());
}

test "explosion fails in LP" {
    try std.testing.expect(explosionFailsExample());
}

test "eval glut conjunction" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .var_ = 0 });
    const na = try arena.f(.{ .not = a });
    const conj = try arena.f(.{ .and_ = .{ .l = a, .r = na } });
    const assign = [_]Four{.b};
    try std.testing.expect(eval(conj, &assign) == .b);
    try std.testing.expect(lpDesignated(conj, &assign));
}
