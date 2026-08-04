//! Higher-order resolution loop — simply-typed clausal fragment.
//!
//! Clauses are sets of typed literals (atomic formula or negation).
//! Binary resolution: complementary atoms with matching types unify under
//! a restricted pattern (first-order style on rigid heads).
//! Factoring collapses duplicate literals.
//!
//! Fragment: propositional-HO (no nested λ in atoms for the loop); full
//! Huet higher-order unification is future work. Enough to refute
//! {P, ¬P} and chain unit resolutions.

const std = @import("std");
const hol = @import("hol.zig");

pub const Literal = struct {
    /// Predicate/constant name of the atom.
    name: []const u8,
    neg: bool = false,
    ty: *hol.Ty,
};

pub const Clause = struct {
    lits: []const Literal,

    pub fn isEmpty(self: Clause) bool {
        return self.lits.len == 0;
    }
};

fn litEql(a: Literal, b: Literal) bool {
    return a.neg == b.neg and std.mem.eql(u8, a.name, b.name) and hol.tyEq(a.ty, b.ty);
}

fn complementary(a: Literal, b: Literal) bool {
    return a.neg != b.neg and std.mem.eql(u8, a.name, b.name) and hol.tyEq(a.ty, b.ty);
}

/// Factor: drop exact duplicate literals.
pub fn factor(allocator: std.mem.Allocator, clause: Clause) !Clause {
    var out: std.ArrayList(Literal) = .empty;
    errdefer out.deinit(allocator);
    for (clause.lits) |l| {
        var dup = false;
        for (out.items) |o| {
            if (litEql(o, l)) {
                dup = true;
                break;
            }
        }
        if (!dup) try out.append(allocator, l);
    }
    return .{ .lits = try out.toOwnedSlice(allocator) };
}

/// Binary resolve on all complementary pairs; returns new clauses (owned).
pub fn resolve(allocator: std.mem.Allocator, a: Clause, b: Clause) ![]Clause {
    var results: std.ArrayList(Clause) = .empty;
    errdefer {
        for (results.items) |c| allocator.free(c.lits);
        results.deinit(allocator);
    }
    for (a.lits, 0..) |la, i| {
        for (b.lits, 0..) |lb, j| {
            if (!complementary(la, lb)) continue;
            var out: std.ArrayList(Literal) = .empty;
            errdefer out.deinit(allocator);
            for (a.lits, 0..) |x, ii| {
                if (ii == i) continue;
                try out.append(allocator, x);
            }
            for (b.lits, 0..) |x, jj| {
                if (jj == j) continue;
                try out.append(allocator, x);
            }
            const raw = Clause{ .lits = try out.toOwnedSlice(allocator) };
            const fac = try factor(allocator, raw);
            allocator.free(raw.lits);
            try results.append(allocator, fac);
        }
    }
    return try results.toOwnedSlice(allocator);
}

pub const ResolveResult = struct {
    status: enum { refuted, saturated, max_steps },
    steps: u32,
};

/// Given set of clauses, run resolution until empty clause or bound.
pub fn refute(allocator: std.mem.Allocator, seed: []const Clause, max_steps: u32) !ResolveResult {
    var active: std.ArrayList(Clause) = .empty;
    defer {
        for (active.items) |c| allocator.free(c.lits);
        active.deinit(allocator);
    }
    for (seed) |c| {
        const copy = try allocator.dupe(Literal, c.lits);
        try active.append(allocator, .{ .lits = copy });
        if (c.isEmpty()) return .{ .status = .refuted, .steps = 0 };
    }

    var steps: u32 = 0;
    var i: usize = 0;
    while (i < active.items.len and steps < max_steps) : (i += 1) {
        var j: usize = 0;
        while (j < i and steps < max_steps) : (j += 1) {
            const news = try resolve(allocator, active.items[i], active.items[j]);
            defer {
                // news clauses moved or freed
            }
            for (news) |n| {
                steps += 1;
                if (n.isEmpty()) {
                    for (news) |m| {
                        if (m.lits.ptr != n.lits.ptr) allocator.free(m.lits);
                    }
                    allocator.free(n.lits);
                    allocator.free(news);
                    return .{ .status = .refuted, .steps = steps };
                }
                // Dedup against active
                var dup = false;
                for (active.items) |a| {
                    if (a.lits.len == n.lits.len) {
                        var same = true;
                        for (a.lits, 0..) |l, k| {
                            if (!litEql(l, n.lits[k])) {
                                same = false;
                                break;
                            }
                        }
                        if (same) {
                            dup = true;
                            break;
                        }
                    }
                }
                if (dup) {
                    allocator.free(n.lits);
                } else {
                    try active.append(allocator, n);
                }
            }
            allocator.free(news);
        }
    }
    if (steps >= max_steps) return .{ .status = .max_steps, .steps = steps };
    return .{ .status = .saturated, .steps = steps };
}

test "resolve P and not P yields empty" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const o = try arena.ty(.bool);
    const p = Literal{ .name = "P", .neg = false, .ty = o };
    const np = Literal{ .name = "P", .neg = true, .ty = o };
    const c1 = Clause{ .lits = &[_]Literal{p} };
    const c2 = Clause{ .lits = &[_]Literal{np} };
    const r = try refute(std.testing.allocator, &[_]Clause{ c1, c2 }, 16);
    try std.testing.expect(r.status == .refuted);
}

test "factor removes duplicates" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const o = try arena.ty(.bool);
    const p = Literal{ .name = "P", .neg = false, .ty = o };
    const c = Clause{ .lits = &[_]Literal{ p, p } };
    const f = try factor(std.testing.allocator, c);
    defer std.testing.allocator.free(f.lits);
    try std.testing.expect(f.lits.len == 1);
}

test "chain resolution refutes" {
    var arena = hol.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const o = try arena.ty(.bool);
    // {P ∨ Q}, {¬P}, {¬Q}
    const p = Literal{ .name = "P", .neg = false, .ty = o };
    const q = Literal{ .name = "Q", .neg = false, .ty = o };
    const np = Literal{ .name = "P", .neg = true, .ty = o };
    const nq = Literal{ .name = "Q", .neg = true, .ty = o };
    const c1 = Clause{ .lits = &[_]Literal{ p, q } };
    const c2 = Clause{ .lits = &[_]Literal{np} };
    const c3 = Clause{ .lits = &[_]Literal{nq} };
    const r = try refute(std.testing.allocator, &[_]Clause{ c1, c2, c3 }, 32);
    try std.testing.expect(r.status == .refuted);
}
