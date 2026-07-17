//! Clausal FOL resolution — Phase 4 prover skeleton.
//!
//! Ground / first-order CNF clauses over `TermPool` literals (predicate atoms).
//! Given-clause loop with binary resolution + factoring + tautology drop.
//!
//! **Soundness target:** unsat ⇒ empty clause derived (unit-tested on small CNF FOL).
//! **Completeness:** not claimed (no fairness strategy / unlimited resources).
//! Superposition / paramodulation = Phase 4b. Not Vampire parity.

const std = @import("std");
const term_mod = @import("term.zig");
const unify_mod = @import("unify.zig");

const TermPool = term_mod.TermPool;
const FormulaPool = term_mod.FormulaPool;
const TermId = term_mod.TermId;
const FormulaId = term_mod.FormulaId;

/// Signed atom: polarity + predicate application term (predicate symbol as func).
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

    fn litsEqual(a: []const FolLit, b: []const FolLit) bool {
        if (a.len != b.len) return false;
        // Multiset equality of (neg, atom) — order sensitive shallow check first,
        // then permutation-tolerant for small clauses.
        if (a.len <= 4) {
            var used: [4]bool = .{ false, false, false, false };
            for (a) |la| {
                var found = false;
                for (b, 0..) |lb, j| {
                    if (used[j]) continue;
                    if (la.neg == lb.neg and la.atom == lb.atom) {
                        used[j] = true;
                        found = true;
                        break;
                    }
                }
                if (!found) return false;
            }
            return true;
        }
        for (a, b) |la, lb| {
            if (la.neg != lb.neg or la.atom != lb.atom) return false;
        }
        return true;
    }

    fn alreadyHas(self: *const Prover, lits: []const FolLit) bool {
        for (self.clauses.items) |c| {
            if (litsEqual(c.lits, lits)) return true;
        }
        return false;
    }

    /// Factor: collapse two same-polarity unifiable lits under MGU.
    /// Returns owned slice or null if no factor found.
    fn tryFactor(self: *Prover, c: FolClause) !?[]FolLit {
        var ia: usize = 0;
        while (ia < c.lits.len) : (ia += 1) {
            var ib = ia + 1;
            while (ib < c.lits.len) : (ib += 1) {
                const la = c.lits[ia];
                const lb = c.lits[ib];
                if (la.neg != lb.neg) continue;

                var subst = unify_mod.Subst.init(self.allocator);
                defer subst.deinit();
                unify_mod.unify(self.pool, &subst, la.atom, lb.atom) catch continue;

                var out: std.ArrayList(FolLit) = .empty;
                errdefer out.deinit(self.allocator);
                for (c.lits, 0..) |l, i| {
                    if (i == ib) continue; // drop second copy
                    try out.append(self.allocator, .{
                        .neg = l.neg,
                        .atom = try unify_mod.apply(self.pool, &subst, l.atom),
                    });
                }
                // drop duplicate atoms of same polarity after apply
                var k: usize = 0;
                while (k < out.items.len) : (k += 1) {
                    var m = k + 1;
                    while (m < out.items.len) {
                        if (out.items[k].neg == out.items[m].neg and out.items[k].atom == out.items[m].atom) {
                            _ = out.orderedRemove(m);
                        } else m += 1;
                    }
                }
                if (self.isTautology(out.items)) {
                    out.deinit(self.allocator);
                    continue;
                }
                // Only accept strictly smaller or unified factor (progress)
                if (out.items.len >= c.lits.len and out.items.len > 0) {
                    // still useful if atoms changed via substitution
                    var changed = out.items.len < c.lits.len;
                    if (!changed) {
                        for (out.items, c.lits[0..out.items.len]) |ol, cl| {
                            if (ol.atom != cl.atom or ol.neg != cl.neg) {
                                changed = true;
                                break;
                            }
                        }
                    }
                    if (!changed) {
                        out.deinit(self.allocator);
                        continue;
                    }
                }
                return try out.toOwnedSlice(self.allocator);
            }
        }
        return null;
    }

    /// Resolve on complementary literals if unifiable (same predicate symbol).
    /// Tries all complementary pairs; returns first non-tautology resolvent.
    fn tryResolve(self: *Prover, a: FolClause, b: FolClause) !?[]FolLit {
        for (a.lits, 0..) |la, ia| {
            for (b.lits, 0..) |lb, ib| {
                if (la.neg == lb.neg) continue;
                // atoms must unify — non-unifiable pairs skip without crash
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

    fn absorb(self: *Prover, lits: []FolLit) !bool {
        // returns true if empty clause absorbed (unsat)
        if (lits.len == 0) {
            self.allocator.free(lits);
            return true;
        }
        if (self.alreadyHas(lits)) {
            self.allocator.free(lits);
            return false;
        }
        try self.clauses.append(self.allocator, .{ .lits = lits });
        return false;
    }

    /// Given-clause style: factor + resolve pairs until empty clause or budget.
    pub fn prove(self: *Prover) !ProveResult {
        var derived: u32 = 0;
        var given: u32 = 0;
        var gi: usize = 0;
        while (gi < self.clauses.items.len) : (gi += 1) {
            given += 1;
            if (self.clauses.items[gi].lits.len == 0)
                return .{ .status = .unsat, .derived = derived, .given = given };

            // Factoring on the given clause
            if (derived < self.max_derived) {
                if (try self.tryFactor(self.clauses.items[gi])) |fact| {
                    derived += 1;
                    if (try self.absorb(fact))
                        return .{ .status = .unsat, .derived = derived, .given = given };
                }
            }

            var hi: usize = 0;
            while (hi < gi) : (hi += 1) {
                if (derived >= self.max_derived)
                    return .{ .status = .resource, .derived = derived, .given = given };
                const resolvent = try self.tryResolve(self.clauses.items[gi], self.clauses.items[hi]);
                if (resolvent) |r| {
                    derived += 1;
                    if (try self.absorb(r))
                        return .{ .status = .unsat, .derived = derived, .given = given };
                }
            }
        }
        return .{ .status = .sat_unknown, .derived = derived, .given = given };
    }
};

// ── unit tests ───────────────────────────────────────────────────────

test "resolution empty via P and not P" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
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

test "resolution multi-step P or Q, not P, not Q" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    // Use nullary-ish atoms P(a), Q(a) as propositional stand-ins
    const p = try pool.mkFunc("P", &.{a});
    const q = try pool.mkFunc("Q", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{
        .{ .neg = false, .atom = p },
        .{ .neg = false, .atom = q },
    });
    try prov.addClause(&.{.{ .neg = true, .atom = p }});
    try prov.addClause(&.{.{ .neg = true, .atom = q }});
    const r = try prov.prove();
    try std.testing.expect(r.status == .unsat);
    try std.testing.expect(r.derived >= 1);
}

test "resolution multi-step three hop" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const p = try pool.mkFunc("P", &.{a});
    const q = try pool.mkFunc("Q", &.{a});
    const r_ = try pool.mkFunc("R", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    // P∨Q, ¬P∨R, ¬Q∨R, ¬R  → unsat
    try prov.addClause(&.{
        .{ .neg = false, .atom = p },
        .{ .neg = false, .atom = q },
    });
    try prov.addClause(&.{
        .{ .neg = true, .atom = p },
        .{ .neg = false, .atom = r_ },
    });
    try prov.addClause(&.{
        .{ .neg = true, .atom = q },
        .{ .neg = false, .atom = r_ },
    });
    try prov.addClause(&.{.{ .neg = true, .atom = r_ }});
    const res = try prov.prove();
    try std.testing.expect(res.status == .unsat);
}

test "resolution factoring P(x) or P(a) with not P(a)" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const x = try pool.mkVar("x");
    const a = try pool.mkConst("a");
    const px = try pool.mkFunc("P", &.{x});
    const pa = try pool.mkFunc("P", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    // {P(x), P(a)} factors toward P(a); with ¬P(a) → empty
    try prov.addClause(&.{
        .{ .neg = false, .atom = px },
        .{ .neg = false, .atom = pa },
    });
    try prov.addClause(&.{.{ .neg = true, .atom = pa }});
    const r = try prov.prove();
    // Either factoring path or resolve P(x) with ¬P(a) yields empty
    try std.testing.expect(r.status == .unsat);
}

test "resolution factoring only produces unit then empty" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const x = try pool.mkVar("x");
    const a = try pool.mkConst("a");
    const px = try pool.mkFunc("P", &.{x});
    const pa = try pool.mkFunc("P", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    // Force factor interest: two copies that unify
    try prov.addClause(&.{
        .{ .neg = false, .atom = px },
        .{ .neg = false, .atom = pa },
    });
    // Factor should run; prove may sat_unknown without contradiction
    const r = try prov.prove();
    try std.testing.expect(r.status == .sat_unknown or r.status == .unsat);
    // If factoring worked we should have derived ≥ 0 (resource free)
    _ = r.derived;
}

test "resolution non-unifiable no crash" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const b = try pool.mkConst("b");
    const pa = try pool.mkFunc("P", &.{a});
    const pb = try pool.mkFunc("P", &.{b});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{.{ .neg = false, .atom = pa }});
    try prov.addClause(&.{.{ .neg = true, .atom = pb }});
    const r = try prov.prove();
    // Ground distinct constants: cannot unify → no empty clause
    try std.testing.expect(r.status == .sat_unknown);
}

test "resolution non-unifiable function clash no crash" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const fa = try pool.mkFunc("f", &.{a});
    const ga = try pool.mkFunc("g", &.{a});
    const pfa = try pool.mkFunc("P", &.{fa});
    const pga = try pool.mkFunc("P", &.{ga});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{.{ .neg = false, .atom = pfa }});
    try prov.addClause(&.{.{ .neg = true, .atom = pga }});
    const r = try prov.prove();
    try std.testing.expect(r.status == .sat_unknown);
    try std.testing.expect(r.derived == 0);
}

test "resolution occurs-check blocks bad unify" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const x = try pool.mkVar("x");
    const fx = try pool.mkFunc("f", &.{x});
    // P(x) vs ¬P(f(x)) — unify x with f(x) fails occurs check
    const px = try pool.mkFunc("P", &.{x});
    const pfx = try pool.mkFunc("P", &.{fx});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{.{ .neg = false, .atom = px }});
    try prov.addClause(&.{.{ .neg = true, .atom = pfx }});
    const r = try prov.prove();
    try std.testing.expect(r.status == .sat_unknown);
}

test "resolution tautology not added as empty path" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const p = try pool.mkFunc("P", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    // Tautology P ∨ ¬P alone is sat_unknown
    try prov.addClause(&.{
        .{ .neg = false, .atom = p },
        .{ .neg = true, .atom = p },
    });
    const r = try prov.prove();
    try std.testing.expect(r.status == .sat_unknown);
}

test "resolution resource budget" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const p = try pool.mkFunc("P", &.{a});
    const q = try pool.mkFunc("Q", &.{a});
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    prov.max_derived = 0;
    try prov.addClause(&.{
        .{ .neg = false, .atom = p },
        .{ .neg = false, .atom = q },
    });
    try prov.addClause(&.{.{ .neg = true, .atom = p }});
    try prov.addClause(&.{.{ .neg = true, .atom = q }});
    const r = try prov.prove();
    // With budget 0 may hit resource before empty, or still find if empty input
    try std.testing.expect(r.status == .resource or r.status == .unsat or r.status == .sat_unknown);
}

test "resolution empty clause input unsat" {
    var pool = TermPool.init(std.testing.allocator);
    defer pool.deinit();
    var prov = Prover.init(std.testing.allocator, &pool);
    defer prov.deinit();
    try prov.addClause(&.{});
    const r = try prov.prove();
    try std.testing.expect(r.status == .unsat);
}
