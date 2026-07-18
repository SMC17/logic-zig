//! Analogical reasoning — Boolean analogical proportions.
//!
//! The Miclet–Prade logical proportion `a : b :: c : d` ("a is to b as c is
//! to d") holds componentwise iff a and b differ exactly the way c and d do:
//!
//!     (a ∧ ¬b) ≡ (c ∧ ¬d)   and   (¬a ∧ b) ≡ (¬c ∧ d)
//!
//! Valid bit patterns: 0000, 1111, 0011, 1100, 0101, 1010. This validates the
//! proportion axioms — reflexivity (a:b::a:b), symmetry (swap pairs), central
//! permutation (swap the means) — and supports **proportion solving**: given
//! a, b, c, the equation a:b::c:x has at most one solution.
//!
//! `classify` performs analogy-based inference: for a query q, every case
//! triple (a,b,c) whose features satisfy a:b::c:q votes with the label
//! solving label(a):label(b)::label(c):x. On affine concepts every solvable
//! vote is exact (it extrapolates to unseen rows); when no triple is
//! label-solvable the classifier abstains instead of guessing.
//!
//! Scope: Boolean vectors; no numerical/structure-mapping analogy yet.

const std = @import("std");

/// Componentwise check of one bit quadruple.
fn bitProportion(a: bool, b: bool, c: bool, d: bool) bool {
    return ((a and !b) == (c and !d)) and ((!a and b) == (!c and d));
}

/// Does a : b :: c : d hold over full vectors?
pub fn holds(a: []const bool, b: []const bool, c: []const bool, d: []const bool) bool {
    std.debug.assert(a.len == b.len and b.len == c.len and c.len == d.len);
    for (a, b, c, d) |x, y, z, w| {
        if (!bitProportion(x, y, z, w)) return false;
    }
    return true;
}

/// Solve one component a : b :: c : x. Null when unsolvable.
pub fn solveBit(a: bool, b: bool, c: bool) ?bool {
    // x = c ⊕ (a ⊕ b) when the pattern is consistent; unsolvable iff a≠b and a≠c.
    if (a == b) return c;
    if (a == c) return b;
    return null; // e.g. 1 0 0 x or 0 1 1 x have no solution
}

/// Solve a : b :: c : x componentwise into `out`. False when unsolvable.
pub fn solve(a: []const bool, b: []const bool, c: []const bool, out: []bool) bool {
    std.debug.assert(a.len == b.len and b.len == c.len and c.len == out.len);
    for (a, b, c, out) |x, y, z, *w| {
        w.* = solveBit(x, y, z) orelse return false;
    }
    return true;
}

pub const Case = struct {
    features: []const bool,
    label: bool,
};

pub const Vote = struct {
    yes: u32 = 0,
    no: u32 = 0,

    pub fn decide(self: Vote) ?bool {
        if (self.yes == self.no) return null;
        return self.yes > self.no;
    }
};

/// Analogy-based classification: triples (a,b,c) of cases with
/// features(a):features(b)::features(c):query vote label(a):label(b)::label(c):x.
pub fn classify(cases: []const Case, query: []const bool) Vote {
    var vote = Vote{};
    for (cases) |ca| {
        for (cases) |cb| {
            for (cases) |cc| {
                if (!holds(ca.features, cb.features, cc.features, query)) continue;
                const x = solveBit(ca.label, cb.label, cc.label) orelse continue;
                if (x) vote.yes += 1 else vote.no += 1;
            }
        }
    }
    return vote;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "analogy: axioms — reflexivity, symmetry, central permutation" {
    var prng = std.Random.DefaultPrng.init(0xA11A);
    const rand = prng.random();
    var iter: u32 = 0;
    while (iter < 200) : (iter += 1) {
        var a: [5]bool = undefined;
        var b: [5]bool = undefined;
        var c: [5]bool = undefined;
        var d: [5]bool = undefined;
        for (0..5) |i| {
            a[i] = rand.boolean();
            b[i] = rand.boolean();
            c[i] = rand.boolean();
            d[i] = rand.boolean();
        }
        // Reflexivity: a:b::a:b always.
        try testing.expect(holds(&a, &b, &a, &b));
        // Inner reflexivity: a:a::b:b always.
        try testing.expect(holds(&a, &a, &b, &b));
        // Symmetry: a:b::c:d ⇔ c:d::a:b.
        try testing.expectEqual(holds(&a, &b, &c, &d), holds(&c, &d, &a, &b));
        // Central permutation: a:b::c:d ⇔ a:c::b:d.
        try testing.expectEqual(holds(&a, &b, &c, &d), holds(&a, &c, &b, &d));
    }
}

test "analogy: exhaustive bit patterns — exactly six valid" {
    var valid: u32 = 0;
    for (0..16) |pat| {
        const a = pat & 8 != 0;
        const b = pat & 4 != 0;
        const c = pat & 2 != 0;
        const d = pat & 1 != 0;
        if (bitProportion(a, b, c, d)) valid += 1;
    }
    try testing.expectEqual(@as(u32, 6), valid);
}

test "analogy: solving returns the unique solution or fails" {
    // Solvable: whenever a solution exists, holds(a,b,c,x) and it is unique.
    for (0..8) |pat| {
        const a = pat & 4 != 0;
        const b = pat & 2 != 0;
        const c = pat & 1 != 0;
        if (solveBit(a, b, c)) |x| {
            try testing.expect(bitProportion(a, b, c, x));
            try testing.expect(!bitProportion(a, b, c, !x)); // uniqueness
        } else {
            try testing.expect(!bitProportion(a, b, c, false));
            try testing.expect(!bitProportion(a, b, c, true));
        }
    }
    // Vector solving.
    var out: [3]bool = undefined;
    try testing.expect(solve(&.{ true, false, true }, &.{ true, true, false }, &.{ false, false, true }, &out));
    try testing.expect(holds(&.{ true, false, true }, &.{ true, true, false }, &.{ false, false, true }, &out));
    // Unsolvable: a=1,b=0,c=0 in some component.
    try testing.expect(!solve(&.{true}, &.{false}, &.{false}, out[0..1]));
}

test "analogy: classification extrapolates an affine concept to an unseen row" {
    // f(x,y) = x, training misses (1,1) entirely.
    const cases = [_]Case{
        .{ .features = &.{ false, false }, .label = false },
        .{ .features = &.{ true, false }, .label = true },
        .{ .features = &.{ false, true }, .label = false },
    };
    const vote = classify(&cases, &.{ true, true });
    try testing.expectEqual(true, vote.decide().?);
    try testing.expectEqual(@as(u32, 0), vote.no); // affine ⇒ unanimous votes
}

test "analogy: leave-one-out on the projection table is perfect and unanimous" {
    const rows = [_]Case{
        .{ .features = &.{ false, false }, .label = false },
        .{ .features = &.{ true, false }, .label = true },
        .{ .features = &.{ false, true }, .label = false },
        .{ .features = &.{ true, true }, .label = true },
    };
    for (0..4) |leave| {
        var train: [3]Case = undefined;
        var k: usize = 0;
        for (rows, 0..) |r, i| {
            if (i != leave) {
                train[k] = r;
                k += 1;
            }
        }
        const vote = classify(&train, rows[leave].features);
        try testing.expectEqual(rows[leave].label, vote.decide().?);
        // Exactness on affine concepts: no dissenting votes.
        if (rows[leave].label) {
            try testing.expectEqual(@as(u32, 0), vote.no);
        } else {
            try testing.expectEqual(@as(u32, 0), vote.yes);
        }
    }
}

test "analogy: minimal XOR training abstains instead of guessing" {
    // With only three XOR rows, every feature-valid triple has an unsolvable
    // label equation (0:1::1:x) — the honest answer is abstention.
    const cases = [_]Case{
        .{ .features = &.{ false, false }, .label = false },
        .{ .features = &.{ true, false }, .label = true },
        .{ .features = &.{ false, true }, .label = true },
    };
    const vote = classify(&cases, &.{ true, true });
    try testing.expect(vote.decide() == null);
    try testing.expectEqual(@as(u32, 0), vote.yes + vote.no);
}
