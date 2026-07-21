//! AGM belief change on finite belief bases.
//!
//! A belief base is a finite list of beliefs, each a small CNF (list of
//! clauses). Contraction K ÷ φ is partial-meet over **remainder sets**
//! (⊆-maximal subsets of K not entailing φ), with three selection policies:
//!
//!   maxichoice    — one remainder (first in enumeration order);
//!   full_meet     — intersection of all remainders (most cautious);
//!   cardinality   — intersection of the maximum-cardinality remainders.
//!
//! Revision K * φ is the Levi identity: contract by ¬φ, then add φ.
//! Entailment is the SAT oracle throughout. The AGM base postulates covered
//! by construction and by tests: success (φ ∉ Cn(K÷φ) when φ not tautological),
//! inclusion (K÷φ ⊆ K), vacuity (φ ∉ Cn(K) ⇒ K÷φ = K), and consistency of
//! revision by a consistent φ.
//!
//! Scope: belief **bases** (finite, syntax-sensitive) — not full deductively
//! closed AGM theories; no epistemic entrenchment ordering yet.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;

/// One belief: a conjunction of clauses (unit list = single clause; a cube
/// is a list of unit clauses).
pub const Belief = struct {
    clauses: []const []const Lit,
};

pub const Selection = enum { maxichoice, full_meet, cardinality };

pub const BaseError = error{
    TooManyBeliefs,
    KeptSetOutOfRange,
};

pub const max_beliefs: u32 = 16;

fn validateBase(base: []const Belief) BaseError!void {
    if (base.len > max_beliefs) return error.TooManyBeliefs;
}

fn fullMask(base_len: usize) u32 {
    return if (base_len == 0) 0 else (@as(u32, 1) << @intCast(base_len)) - 1;
}

fn addBelief(theory: *Cnf, b: Belief) !void {
    for (b.clauses) |c| try theory.addClause(c);
}

fn buildTheory(allocator: std.mem.Allocator, base: []const Belief, selected: u32) !Cnf {
    var t = Cnf.init(allocator);
    errdefer t.deinit();
    for (base, 0..) |b, i| {
        for (b.clauses) |c| {
            for (c) |l| t.ensureVars(l.variable().index() + 1);
        }
        if ((selected >> @intCast(i)) & 1 == 1) try addBelief(&t, b);
    }
    return t;
}

/// Does the selected sub-base entail the target (a CNF: every clause entailed)?
fn entailsTarget(
    allocator: std.mem.Allocator,
    base: []const Belief,
    selected: u32,
    target: Belief,
) !bool {
    for (target.clauses) |clause| {
        var t = try buildTheory(allocator, base, selected);
        defer t.deinit();
        // ¬clause as unit cubes.
        for (clause) |l| {
            t.ensureVars(l.variable().index() + 1);
            try t.addClause(&.{l.not()});
        }
        const r = try solver_mod.solveCnf(allocator, &t, .{});
        defer if (r.model) |m| allocator.free(m);
        if (r.status != .unsat) return false;
    }
    return true;
}

pub const Remainders = struct {
    allocator: std.mem.Allocator,
    /// ⊆-maximal non-entailing subsets, as bitmasks over belief indices.
    sets: std.ArrayList(u32) = .empty,

    pub fn deinit(self: *Remainders) void {
        self.sets.deinit(self.allocator);
        self.* = undefined;
    }
};

/// Remainder sets K ⊥ φ (maximal subsets of the base not entailing φ).
pub fn remainders(
    allocator: std.mem.Allocator,
    base: []const Belief,
    target: Belief,
) !Remainders {
    try validateBase(base);
    var out = Remainders{ .allocator = allocator };
    errdefer out.deinit();
    const n: u5 = @intCast(base.len);
    const total: u32 = @as(u32, 1) << n;
    var candidates: std.ArrayList(u32) = .empty;
    defer candidates.deinit(allocator);
    var s: u32 = 0;
    while (s < total) : (s += 1) {
        if (!try entailsTarget(allocator, base, s, target)) {
            try candidates.append(allocator, s);
        }
    }
    for (candidates.items) |a| {
        var maximal = true;
        for (candidates.items) |b| {
            if (a != b and (a & b) == a) {
                maximal = false;
                break;
            }
        }
        if (maximal) try out.sets.append(allocator, a);
    }
    return out;
}

/// Verify the exact family K perpendicular phi: each claimed set is a unique,
/// maximal non-entailing sub-base, and no such sub-base is omitted.
pub fn verifyRemainders(
    allocator: std.mem.Allocator,
    base: []const Belief,
    target: Belief,
    claimed: []const u32,
) !bool {
    try validateBase(base);
    const full = fullMask(base.len);
    for (claimed, 0..) |set, index| {
        if (set & ~full != 0) return false;
        for (claimed[index + 1 ..]) |other| if (set == other) return false;
    }
    const total: u32 = full + 1;
    var candidate: u32 = 0;
    while (candidate < total) : (candidate += 1) {
        var expected = !try entailsTarget(allocator, base, candidate, target);
        if (expected) {
            var superset: u32 = 0;
            while (superset < total) : (superset += 1) {
                if (candidate != superset and (candidate & superset) == candidate and
                    !try entailsTarget(allocator, base, superset, target))
                {
                    expected = false;
                    break;
                }
            }
        }
        var present = false;
        for (claimed) |set| if (set == candidate) {
            present = true;
            break;
        };
        if (present != expected) return false;
    }
    return true;
}

pub const ChangeResult = struct {
    allocator: std.mem.Allocator,
    /// Kept belief indices as a bitmask over the input base.
    kept: u32,
    /// For revision: the added formula must be conjoined by the caller
    /// (returned base indices never include it).
    pub fn deinit(self: *ChangeResult) void {
        self.* = undefined;
    }

    pub fn keeps(self: ChangeResult, i: u32) bool {
        return (self.kept >> @intCast(i)) & 1 == 1;
    }
};

/// Partial-meet contraction K ÷ φ.
pub fn contract(
    allocator: std.mem.Allocator,
    base: []const Belief,
    target: Belief,
    selection: Selection,
) !ChangeResult {
    try validateBase(base);
    // Tautological target has no remainders except... every subset entails ⊤;
    // AGM: K ÷ ⊤ = K. Detect: full base does not entail target? then vacuity.
    const full = fullMask(base.len);
    if (!try entailsTarget(allocator, base, full, target)) {
        return .{ .allocator = allocator, .kept = full }; // vacuity
    }
    var rem = try remainders(allocator, base, target);
    defer rem.deinit();
    if (rem.sets.items.len == 0) {
        // φ tautological (entailed even by ∅): keep everything (AGM failure case).
        return .{ .allocator = allocator, .kept = full };
    }
    const kept: u32 = switch (selection) {
        .maxichoice => rem.sets.items[0],
        .full_meet => blk: {
            var acc: u32 = full;
            for (rem.sets.items) |r| acc &= r;
            break :blk acc;
        },
        .cardinality => blk: {
            var best: u32 = 0;
            for (rem.sets.items) |r| {
                if (@popCount(r) > @popCount(best)) best = r;
            }
            var acc: u32 = full;
            for (rem.sets.items) |r| {
                if (@popCount(r) == @popCount(best)) acc &= r;
            }
            break :blk acc;
        },
    };
    return .{ .allocator = allocator, .kept = kept };
}

/// Replay a contraction result from exact remainders and the selected partial-
/// meet policy. Maxichoice deliberately uses the deterministic enumeration order.
pub fn verifyContraction(
    allocator: std.mem.Allocator,
    base: []const Belief,
    target: Belief,
    selection: Selection,
    result: ChangeResult,
) !bool {
    try validateBase(base);
    const full = fullMask(base.len);
    if (result.kept & ~full != 0) return false;
    const entailed = try entailsTarget(allocator, base, full, target);
    if (!entailed) return result.kept == full;
    var rem = try remainders(allocator, base, target);
    defer rem.deinit();
    if (!try verifyRemainders(allocator, base, target, rem.sets.items)) return false;
    if (rem.sets.items.len == 0) return result.kept == full;
    const expected: u32 = switch (selection) {
        .maxichoice => rem.sets.items[0],
        .full_meet => blk: {
            var intersection = full;
            for (rem.sets.items) |set| intersection &= set;
            break :blk intersection;
        },
        .cardinality => blk: {
            var best_size: u32 = 0;
            for (rem.sets.items) |set| best_size = @max(best_size, @popCount(set));
            var intersection = full;
            for (rem.sets.items) |set| {
                if (@popCount(set) == best_size) intersection &= set;
            }
            break :blk intersection;
        },
    };
    return result.kept == expected;
}

/// Levi-identity revision K * φ: contract by ¬φ, then add φ.
/// φ must be a **cube** here (so ¬φ is a single clause). Returns the kept
/// sub-base; the caller conjoins φ itself.
pub fn revise(
    allocator: std.mem.Allocator,
    base: []const Belief,
    phi_cube: []const Lit,
    selection: Selection,
) !ChangeResult {
    var neg_clause = try allocator.alloc(Lit, phi_cube.len);
    defer allocator.free(neg_clause);
    for (phi_cube, 0..) |l, i| neg_clause[i] = l.not();
    const neg_target = Belief{ .clauses = &.{neg_clause} };
    return contract(allocator, base, neg_target, selection);
}

/// Replay Levi revision evidence by reconstructing contraction by `not phi`.
/// The returned bitmask certifies the retained sub-base; `phi_cube` is the
/// explicit added belief and is therefore not encoded as a base index.
pub fn verifyRevision(
    allocator: std.mem.Allocator,
    base: []const Belief,
    phi_cube: []const Lit,
    selection: Selection,
    result: ChangeResult,
) !bool {
    var neg_clause = try allocator.alloc(Lit, phi_cube.len);
    defer allocator.free(neg_clause);
    for (phi_cube, 0..) |literal, index| neg_clause[index] = literal.not();
    const neg_target = Belief{ .clauses = &.{neg_clause} };
    return verifyContraction(allocator, base, neg_target, selection, result);
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;
const Var = lit_mod.Var;

fn lp(v: u32) Lit {
    return Lit.positive(Var.fromIndex(v));
}
fn ln(v: u32) Lit {
    return Lit.negative(Var.fromIndex(v));
}

// Base: {p, p→q, q→r} — entails q and r.
const b_p = Belief{ .clauses = &.{&.{lp(0)}} };
const b_pq = Belief{ .clauses = &.{&.{ ln(0), lp(1) }} };
const b_qr = Belief{ .clauses = &.{&.{ ln(1), lp(2) }} };
const base3 = [_]Belief{ b_p, b_pq, b_qr };

test "agm: remainders of q are the maximal q-free subsets" {
    var rem = try remainders(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} });
    defer rem.deinit();
    // K⊥q: {p, q→r} and {p→q, q→r}.
    try testing.expectEqual(@as(usize, 2), rem.sets.items.len);
    var found_a = false;
    var found_b = false;
    for (rem.sets.items) |s| {
        if (s == 0b101) found_a = true;
        if (s == 0b110) found_b = true;
    }
    try testing.expect(found_a and found_b);
}

test "agm: success — contraction removes entailment of q" {
    inline for (.{ Selection.maxichoice, Selection.full_meet, Selection.cardinality }) |sel| {
        var c = try contract(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} }, sel);
        defer c.deinit();
        try testing.expect(!try entailsTarget(testing.allocator, &base3, c.kept, .{ .clauses = &.{&.{lp(1)}} }));
        // Inclusion: kept ⊆ base by construction (bitmask over base).
    }
}

test "agm: full-meet is the intersection — most cautious" {
    var c = try contract(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} }, .full_meet);
    defer c.deinit();
    // Intersection of {p,q→r} and {p→q,q→r} = {q→r}.
    try testing.expectEqual(@as(u32, 0b100), c.kept);
}

test "agm: vacuity — contracting something not entailed changes nothing" {
    var c = try contract(testing.allocator, &base3, .{ .clauses = &.{&.{lp(5)}} }, .maxichoice);
    defer c.deinit();
    try testing.expectEqual(@as(u32, 0b111), c.kept);
}

test "agm: tautology contraction keeps the base (failure postulate)" {
    var c = try contract(testing.allocator, &base3, .{ .clauses = &.{&.{ lp(4), ln(4) }} }, .full_meet);
    defer c.deinit();
    try testing.expectEqual(@as(u32, 0b111), c.kept);
}

test "agm: revision by ¬p is consistent and retains what it can" {
    var c = try revise(testing.allocator, &base3, &.{ln(0)}, .full_meet);
    defer c.deinit();
    // Kept sub-base plus ¬p must be consistent.
    var t = try buildTheory(testing.allocator, &base3, c.kept);
    defer t.deinit();
    try t.addClause(&.{ln(0)});
    const r = try solver_mod.solveCnf(testing.allocator, &t, .{});
    defer if (r.model) |m| testing.allocator.free(m);
    try testing.expect(r.status == .sat);
    // p itself must be gone.
    try testing.expect(!c.keeps(0));
    // Success of the underlying contraction: kept base does not entail p.
    try testing.expect(!try entailsTarget(testing.allocator, &base3, c.kept, .{ .clauses = &.{&.{lp(0)}} }));
    try testing.expect(try verifyRevision(testing.allocator, &base3, &.{ln(0)}, .full_meet, c));
}

test "agm: cardinality selection prefers larger remainders" {
    // Base: {p, q, p∧q→r}; contract r. Remainders: {p,q}? no — {p,q} entails? p∧q∧(p∧q→r) — without third belief {p,q} doesn't entail r. Remainders: {p,q}, and {p∧q→r, p}, {p∧q→r, q}? all size 2… all maximal size-2 sets fail to entail r.
    const bp = Belief{ .clauses = &.{&.{lp(0)}} };
    const bq = Belief{ .clauses = &.{&.{lp(1)}} };
    const bpqr = Belief{ .clauses = &.{&.{ ln(0), ln(1), lp(2) }} };
    const base = [_]Belief{ bp, bq, bpqr };
    var rem = try remainders(testing.allocator, &base, .{ .clauses = &.{&.{lp(2)}} });
    defer rem.deinit();
    try testing.expectEqual(@as(usize, 3), rem.sets.items.len);
    var c = try contract(testing.allocator, &base, .{ .clauses = &.{&.{lp(2)}} }, .cardinality);
    defer c.deinit();
    // All remainders have cardinality 2 → intersection of all three = ∅.
    try testing.expectEqual(@as(u32, 0), c.kept);
}

test "agm: exact remainder and contraction evidence replays exhaustively on sub-bases" {
    const universe = [_]Belief{
        .{ .clauses = &.{&.{lp(0)}} },
        .{ .clauses = &.{&.{lp(1)}} },
        .{ .clauses = &.{&.{ ln(0), lp(1) }} },
        .{ .clauses = &.{&.{ ln(1), lp(2) }} },
    };
    var base: std.ArrayList(Belief) = .empty;
    defer base.deinit(testing.allocator);
    const targets = [_]Belief{
        .{ .clauses = &.{&.{lp(0)}} },
        .{ .clauses = &.{&.{lp(1)}} },
        .{ .clauses = &.{&.{lp(2)}} },
    };
    var choice: u32 = 0;
    while (choice < (@as(u32, 1) << universe.len)) : (choice += 1) {
        base.clearRetainingCapacity();
        for (universe, 0..) |belief, index| {
            if ((choice >> @intCast(index)) & 1 == 1) try base.append(testing.allocator, belief);
        }
        for (targets) |target| {
            var rem = try remainders(testing.allocator, base.items, target);
            try testing.expect(try verifyRemainders(testing.allocator, base.items, target, rem.sets.items));
            rem.deinit();
            for (std.enums.values(Selection)) |selection| {
                var result = try contract(testing.allocator, base.items, target, selection);
                try testing.expect(try verifyContraction(testing.allocator, base.items, target, selection, result));
                result.deinit();
            }
        }
    }
}

test "agm: malformed bases and mutated evidence fail closed" {
    const repeated = [_]Belief{b_p} ** 17;
    try testing.expectError(error.TooManyBeliefs, remainders(testing.allocator, &repeated, b_p));
    var rem = try remainders(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} });
    defer rem.deinit();
    try testing.expect(try verifyRemainders(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} }, rem.sets.items));
    _ = rem.sets.pop();
    try testing.expect(!(try verifyRemainders(testing.allocator, &base3, .{ .clauses = &.{&.{lp(1)}} }, rem.sets.items)));
    var invalid = ChangeResult{ .allocator = testing.allocator, .kept = 0b1000 };
    defer invalid.deinit();
    try testing.expect(!(try verifyContraction(testing.allocator, &base3, b_p, .full_meet, invalid)));
}
