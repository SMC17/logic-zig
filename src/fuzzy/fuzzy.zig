//! Fuzzy / many-valued propositional logic — fragment for universal library.
//!
//! Truth degrees in [0, 1] (f32). Connectives parameterized by a t-norm family:
//!   - Gödel / min:       t = min, s = max,  → = 1 if a≤b else b
//!   - Product:           t = a*b, s = a+b-a*b, → = 1 if a≤b else b/a
//!   - Łukasiewicz:       t = max(0,a+b-1), s = min(1,a+b), → = min(1,1-a+b)
//!
//! Also ships a 3-valued Kleene evaluator (true / false / unknown) as the
//! discrete many-valued entry point.
//!
//! Not a full fuzzy inference system (Mamdani/TSK); those can sit on top later.

const std = @import("std");

pub const Degree = f32;

pub const TNorm = enum {
    godel,
    product,
    lukasiewicz,
};

pub fn tnorm(family: TNorm, a: Degree, b: Degree) Degree {
    return switch (family) {
        .godel => @min(a, b),
        .product => a * b,
        .lukasiewicz => @max(@as(Degree, 0), a + b - 1),
    };
}

pub fn tconorm(family: TNorm, a: Degree, b: Degree) Degree {
    return switch (family) {
        .godel => @max(a, b),
        .product => a + b - a * b,
        .lukasiewicz => @min(@as(Degree, 1), a + b),
    };
}

pub fn neg(a: Degree) Degree {
    return 1 - a;
}

pub fn implies(family: TNorm, a: Degree, b: Degree) Degree {
    return switch (family) {
        .godel => if (a <= b) @as(Degree, 1) else b,
        .product => if (a <= b) @as(Degree, 1) else b / a,
        .lukasiewicz => @min(@as(Degree, 1), 1 - a + b),
    };
}

pub fn equiv(family: TNorm, a: Degree, b: Degree) Degree {
    return tnorm(family, implies(family, a, b), implies(family, b, a));
}

/// Fuzzy formula over named variables (indices into an assignment array).
pub const FuzzyFormula = union(enum) {
    const_: Degree,
    var_: u32,
    not: *FuzzyFormula,
    and_: struct { l: *FuzzyFormula, r: *FuzzyFormula },
    or_: struct { l: *FuzzyFormula, r: *FuzzyFormula },
    implies: struct { l: *FuzzyFormula, r: *FuzzyFormula },
    iff: struct { l: *FuzzyFormula, r: *FuzzyFormula },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*FuzzyFormula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn f(self: *Arena, v: FuzzyFormula) !*FuzzyFormula {
        const p = try self.allocator.create(FuzzyFormula);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

pub fn eval(family: TNorm, phi: *const FuzzyFormula, assign: []const Degree) Degree {
    return switch (phi.*) {
        .const_ => |c| c,
        .var_ => |i| assign[i],
        .not => |n| neg(eval(family, n, assign)),
        .and_ => |a| tnorm(family, eval(family, a.l, assign), eval(family, a.r, assign)),
        .or_ => |a| tconorm(family, eval(family, a.l, assign), eval(family, a.r, assign)),
        .implies => |a| implies(family, eval(family, a.l, assign), eval(family, a.r, assign)),
        .iff => |a| equiv(family, eval(family, a.l, assign), eval(family, a.r, assign)),
    };
}

/// Degree of satisfiability under a fixed assignment (just eval).
/// For ∃-sat degree one would maximise over assignments — later.
pub fn satDegree(family: TNorm, phi: *const FuzzyFormula, assign: []const Degree) Degree {
    return eval(family, phi, assign);
}

// ---------- 3-valued Kleene (finite many-valued entry) ----------

pub const Kleene = enum { false_, unknown, true_ };

pub fn kleeneNot(v: Kleene) Kleene {
    return switch (v) {
        .false_ => .true_,
        .true_ => .false_,
        .unknown => .unknown,
    };
}

pub fn kleeneAnd(a: Kleene, b: Kleene) Kleene {
    if (a == .false_ or b == .false_) return .false_;
    if (a == .unknown or b == .unknown) return .unknown;
    return .true_;
}

pub fn kleeneOr(a: Kleene, b: Kleene) Kleene {
    if (a == .true_ or b == .true_) return .true_;
    if (a == .unknown or b == .unknown) return .unknown;
    return .false_;
}

test "lukasiewicz t-norm bounds" {
    try std.testing.expect(tnorm(.lukasiewicz, 0.7, 0.6) == @as(Degree, 0.3));
    try std.testing.expect(tnorm(.lukasiewicz, 0.2, 0.3) == @as(Degree, 0));
    try std.testing.expect(implies(.lukasiewicz, 0.3, 0.8) == @as(Degree, 1));
}

test "godel implication" {
    try std.testing.expect(implies(.godel, 0.4, 0.9) == @as(Degree, 1));
    try std.testing.expect(implies(.godel, 0.9, 0.4) == @as(Degree, 0.4));
}

test "fuzzy eval modus ponens degree" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    // (p → q) ∧ p   under p=0.8, q=0.5  with Łukasiewicz
    const p = try arena.f(.{ .var_ = 0 });
    const q = try arena.f(.{ .var_ = 1 });
    const imp = try arena.f(.{ .implies = .{ .l = p, .r = q } });
    const conj = try arena.f(.{ .and_ = .{ .l = imp, .r = p } });
    const assign = [_]Degree{ 0.8, 0.5 };
    const d = eval(.lukasiewicz, conj, &assign);
    // (p→q) = min(1, 1-0.8+0.5) = 0.7;  0.7 ∧ 0.8 = max(0,0.7+0.8-1)=0.5
    try std.testing.expect(@abs(d - 0.5) < 1e-5);
}

test "kleene three-valued" {
    try std.testing.expect(kleeneAnd(.true_, .unknown) == .unknown);
    try std.testing.expect(kleeneOr(.false_, .unknown) == .unknown);
    try std.testing.expect(kleeneAnd(.false_, .unknown) == .false_);
    try std.testing.expect(kleeneNot(.unknown) == .unknown);
}
