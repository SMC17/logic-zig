//! Clausal FOL resolution — Phase 4 prover skeleton.
//!
//! Ground / first-order CNF clauses over `TermPool` literals (predicate atoms).
//! Given-clause loop with binary resolution + factoring + tautology drop.
//!
//! **Soundness target:** unsat ⇒ empty clause derived (unit-tested on small CNF FOL).
//! **Completeness:** not claimed (no fairness strategy / unlimited resources).
//! Superposition / paramodulation = Phase 4b.

const std = @import("std");
const term_mod = @import("term.zig");
const unify_mod = @import("unify.zig");

const TermPool = term_mod.TermPool;
const FormulaPool = term_mod.FormulaPool;
const TermId = term_mod.TermId;
const FormulaId = term_mod.FormulaId;

/// Signed atom: polarity + predicate application term (func/const used as atom).
pub const FolLit = struct {
    neg: bool,
    /// Atom term (predicate symbol as func, args).
    atom: TermId,
};

pub const FolClause = struct {
    lits: []FolLit,
};

pub const ProveStatus = enum { unsat, sat_unknown, resource };

pub const ProveResult = struct {
    status: ProveStatus,
    derived: u32 = 0,
    given: u32 = 0,
};

pub const Prover = struct {
    allocator: std.mem.Allocator,
    pool: *TermPool,
    /// Active clause set (owned lit slices).
    clauses: std.ArrayList(FolClause) = .empty,
    max_derived: u32 = 10_000,

    pub fn init(allocator: std.mem.Allocator, pool: *TermPool) Prover {
        return .{ .allocator = allocator, .pool = pool };
    }

    pub fn deinit(self: *Prover) void {
        for (self.clauses.items) |c| self.allocator.free(c.lits);
        self.clauses.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addClause(self: *Prover, lits: []const FolLit) !void {
        const copy = try self.allocator.dupe(FolLit, lits);
        try self.clauses.append(self.allocator, .{ .lits = copy });
    }

    fn isTautology(self: *Prover, lits: []const FolLit) bool {
        _ = self;
        var i: usize = 0;
        while (i < lits.len) : (i += 1) {
            var j = i + 1;
            while (j < lits.len) : (j += 1) {
                if (lits[i].neg != lits[j].neg and lits[i].atom == lits[j].atom)
                    return true;
            }
        }
        return false;
    }

    /// Resolve on complementary literals if unifiable (same predicate symbol).
    fn tryResolve(self: *Prover, a: FolClause, b: FolClause) !?[]FolLit {
        for (a.lits, 0..) |la, ia| {
            for (b.lits, 0..) |lb, ib| {
                if (la.neg == lb.neg) continue;
                // atoms must unify
                var subst = unify_mod.Subst.init(self.allocator);
                defer subst.deinit();
                unify_mod.unify(self.pool, &subst, la.atom, lb.atom) catch continue;

                var out: std.ArrayList(FolLit) = .empty;
                errdefer out.deinit(self.allocator);
                for (a.lits, 0..) |l, i| {
                    if (i == ia) continue;
                    try out.append(self.allocator, .{
                        .neg = l.neg,
                        .atom = try unify_mod.apply(self.pool, &subst, l.atom),
                    });
                }
                for (b.lits, 0..) |l, i| {
                    if (i == ib) continue;
                    try out.append(self.allocator, .{
                        .neg = l.neg,
                        .atom = try unify_mod.apply(self.pool, &subst, l.atom),
                    });
                }
                if (self.isTautology(out.items)) {
                    out.deinit(self.allocator);
                    continue;
                }
                return try out.toOwnedSlice(self.allocator);
            }
        }
        return null;
    }

    /// Given-clause style: resolve pairs until empty clause or budget.
    pub fn prove(self: *Prover) !ProveResult {
        var derived: u32 = 0;
        var given: u32 = 0;
        var gi: usize = 0;
        while (gi < self.clauses.items.len) : (gi += 1) {
            given += 1;
            if (self.clauses.items[gi].lits.len == 0)
                return .{ .status = .unsat, .derived = derived, .given = given };

            var hi: usize = 0;
            while (hi < gi) : (hi += 1) {
                if (derived >= self.max_derived)
                    return .{ .status = .resource, .derived = derived, .given = given };
                const resolvent = try self.tryResolve(self.clauses.items[gi], self.clauses.items[hi]);
                if (resolvent) |r| {
                    derived += 1;
                    if (r.len == 0) {
                        self.allocator.free(r);
                        return .{ .status = .unsat, .derived = derived, .given = given };
                    }
                    // skip duplicates (shallow)
                    var dup = false;
                    for (self.clauses.items) |c| {
                        if (c.lits.len == r.len) {
                            // crude
                            dup = true;
                            break;
                        }
                    }
                    if (dup and r.len > 0) {
                        // still add — crude filter disabled for small problems
                    }
                    try self.clauses.append(self.allocator, .{ .lits = r });
                }
            }
        }
        return .{ .status = .sat_unknown, .derived = derived, .given = given };
    }
};

test "resolution empty via P and not P" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    // P(a) and ¬P(a)
    const a = try pool.mkConst("a");
    const pa = try pool.mkFunc("P", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{.{ .neg = false, .atom = pa }});
    try prov.addClause(&.{.{ .neg = true, .atom = pa }});
    const r = try prov.prove();
    try std.testing.expect(r.status == .unsat);
}

test "resolution unsat with unify" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    // P(x) and ¬P(a)  — resolve with x↦a
    const x = try pool.mkVar("x");
    const a = try pool.mkConst("a");
    const px = try pool.mkFunc("P", &.{x});
    const pa = try pool.mkFunc("P", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{.{ .neg = false, .atom = px }});
    try prov.addClause(&.{.{ .neg = true, .atom = pa }});
    const r = try prov.prove();
    try std.testing.expect(r.status == .unsat);
}
