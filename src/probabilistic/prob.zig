//! Probabilistic logic — atomic probabilities + independence fragment.
//!
//! Assign P(atom) ∈ [0,1]. Under mutual independence:
//!   P(A ∧ B) = P(A)·P(B)
//!   P(A ∨ B) = P(A)+P(B)−P(A)·P(B)
//!   P(¬A)    = 1−P(A)
//!
//! Entailment bounds without full independence use Fréchet inequalities:
//!   max(0, P(A)+P(B)−1) ≤ P(A∧B) ≤ min(P(A),P(B))
//!
//! Fragment: formula evaluator under independence + Fréchet bound helpers.
//! Not a full probabilistic theorem prover / Markov logic network.

const std = @import("std");

pub const Prob = f64;

pub const Formula = union(enum) {
    atom: u32,
    const_: Prob,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
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

/// Evaluate under mutual independence of atoms.
pub fn evalIndep(phi: *const Formula, p_atom: []const Prob) Prob {
    return switch (phi.*) {
        .const_ => |c| c,
        .atom => |i| p_atom[i],
        .not => |n| 1.0 - evalIndep(n, p_atom),
        .and_ => |a| evalIndep(a.l, p_atom) * evalIndep(a.r, p_atom),
        .or_ => |a| blk: {
            const x = evalIndep(a.l, p_atom);
            const y = evalIndep(a.r, p_atom);
            break :blk x + y - x * y;
        },
    };
}

pub const Interval = struct {
    lo: Prob,
    hi: Prob,
};

/// Fréchet bounds for conjunction given marginals.
pub fn frechetAnd(pa: Prob, pb: Prob) Interval {
    return .{ .lo = @max(@as(Prob, 0), pa + pb - 1), .hi = @min(pa, pb) };
}

/// Fréchet bounds for disjunction given marginals.
pub fn frechetOr(pa: Prob, pb: Prob) Interval {
    return .{ .lo = @max(pa, pb), .hi = @min(@as(Prob, 1), pa + pb) };
}

test "independence product" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = 0 });
    const b = try arena.f(.{ .atom = 1 });
    const conj = try arena.f(.{ .and_ = .{ .l = a, .r = b } });
    const ps = [_]Prob{ 0.5, 0.4 };
    try std.testing.expect(@abs(evalIndep(conj, &ps) - 0.2) < 1e-12);
}

test "frechet and bounds" {
    const iv = frechetAnd(0.7, 0.6);
    try std.testing.expect(iv.lo == 0.3);
    try std.testing.expect(iv.hi == 0.6);
}

test "negation complement" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = 0 });
    const na = try arena.f(.{ .not = a });
    const ps = [_]Prob{0.3};
    try std.testing.expect(@abs(evalIndep(na, &ps) - 0.7) < 1e-12);
}
