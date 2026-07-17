//! KLM-style defeasible consequence — rational closure (Lehmann–Magidor).
//!
//! A conditional knowledge base is a set of defeasible rules α |~ β
//! ("if α, normally β") with α, β cubes of literals, plus optional hard
//! background knowledge (CNF). Rational closure is computed by the standard
//! exceptionality iteration:
//!
//!   E_0 = all rules; E_{i+1} = { r ∈ E_i : antecedent(r) exceptional in E_i }
//!
//! where α is *exceptional* in a rule set R iff the material counterpart of R
//! (α→β for each rule) together with the background entails ¬α. The first
//! level a rule drops out is its rank; rules never dropping out are totally
//! exceptional (infinite rank). A query α |~ β holds in the rational closure
//! iff, at the lowest level i where α is consistent with materialize(E_i),
//! that theory entails α→β. All checks are single SAT calls.
//!
//! This validates the KLM rational-consequence postulates by construction and
//! gets the canonical behaviors right: specificity overrides, irrelevance
//! preserved, and nonmonotonicity (bird |~ fly yet penguin·bird |~ ¬fly).

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Lit = lit_mod.Lit;

pub const Conditional = struct {
    /// Cube (conjunction of literals). Empty = ⊤.
    antecedent: []const Lit,
    /// Cube. Empty = ⊤.
    consequent: []const Lit,
};

pub const infinite_rank: u32 = std.math.maxInt(u32);

pub const Ranking = struct {
    allocator: std.mem.Allocator,
    /// Rank per rule (parallel to the KB); `infinite_rank` = totally exceptional.
    ranks: []u32,
    /// Number of finite levels (0..levels-1 are meaningful E_i sets).
    levels: u32,

    pub fn deinit(self: *Ranking) void {
        self.allocator.free(self.ranks);
        self.* = undefined;
    }
};

fn addBackground(out: *Cnf, background: ?*const Cnf) !void {
    if (background) |bg| {
        out.ensureVars(bg.num_vars);
        for (0..bg.numClauses()) |ci| {
            try out.addClause(bg.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
        }
    }
}

/// Add material counterparts α→β for every rule with `active[i]`.
fn addMaterialized(
    allocator: std.mem.Allocator,
    out: *Cnf,
    kb: []const Conditional,
    active: []const bool,
) !void {
    var buf: std.ArrayList(Lit) = .empty;
    defer buf.deinit(allocator);
    for (kb, active) |r, on| {
        if (!on) continue;
        for (r.antecedent) |l| out.ensureVars(l.variable().index() + 1);
        // α→(c1∧…∧cn) as clauses (¬α ∨ cj).
        for (r.consequent) |c| {
            buf.clearRetainingCapacity();
            for (r.antecedent) |l| try buf.append(allocator, l.not());
            try buf.append(allocator, c);
            try out.addClause(buf.items);
        }
        // Rule with empty consequent (⊤): nothing to add.
    }
}

fn cubeConsistentWith(
    allocator: std.mem.Allocator,
    background: ?*const Cnf,
    kb: []const Conditional,
    active: []const bool,
    cube: []const Lit,
    extra_neg_cube: ?[]const Lit,
) !bool {
    var theory = Cnf.init(allocator);
    defer theory.deinit();
    try addBackground(&theory, background);
    try addMaterialized(allocator, &theory, kb, active);
    for (cube) |l| {
        theory.ensureVars(l.variable().index() + 1);
        try theory.addClause(&.{l});
    }
    if (extra_neg_cube) |nc| {
        // ¬(c1∧…∧cn) as one clause of negations.
        var buf: std.ArrayList(Lit) = .empty;
        defer buf.deinit(allocator);
        for (nc) |l| {
            theory.ensureVars(l.variable().index() + 1);
            try buf.append(allocator, l.not());
        }
        try theory.addClause(buf.items);
    }
    const r = try solver_mod.solveCnf(allocator, &theory, .{});
    defer if (r.model) |m| allocator.free(m);
    return r.status == .sat;
}

/// Compute the rational-closure ranking of a conditional KB.
pub fn rank(
    allocator: std.mem.Allocator,
    background: ?*const Cnf,
    kb: []const Conditional,
) !Ranking {
    const ranks = try allocator.alloc(u32, kb.len);
    errdefer allocator.free(ranks);
    @memset(ranks, infinite_rank);
    const active = try allocator.alloc(bool, kb.len);
    defer allocator.free(active);
    @memset(active, true);

    var level: u32 = 0;
    while (true) : (level += 1) {
        var dropped: u32 = 0;
        var remaining: u32 = 0;
        // A rule survives to the next level iff its antecedent is exceptional
        // (inconsistent with the current level's materialization).
        const next = try allocator.alloc(bool, kb.len);
        defer allocator.free(next);
        for (kb, 0..) |r, i| {
            if (!active[i]) {
                next[i] = false;
                continue;
            }
            const consistent = try cubeConsistentWith(allocator, background, kb, active, r.antecedent, null);
            if (consistent) {
                ranks[i] = level;
                next[i] = false;
                dropped += 1;
            } else {
                next[i] = true;
                remaining += 1;
            }
        }
        @memcpy(active, next);
        if (dropped == 0) {
            // Fixpoint: remaining rules are totally exceptional.
            return .{ .allocator = allocator, .ranks = ranks, .levels = level };
        }
        if (remaining == 0) {
            return .{ .allocator = allocator, .ranks = ranks, .levels = level + 1 };
        }
    }
}

pub const QueryResult = struct {
    entailed: bool,
    /// Level at which the antecedent became consistent; null when it never
    /// does (antecedent impossible → vacuously entailed).
    level: ?u32,
};

/// Does α |~ β hold in the rational closure of the KB?
pub fn query(
    allocator: std.mem.Allocator,
    background: ?*const Cnf,
    kb: []const Conditional,
    ranking: *const Ranking,
    antecedent: []const Lit,
    consequent: []const Lit,
) !QueryResult {
    const active = try allocator.alloc(bool, kb.len);
    defer allocator.free(active);

    var level: u32 = 0;
    while (level <= ranking.levels) : (level += 1) {
        for (kb, 0..) |_, i| active[i] = ranking.ranks[i] >= level;
        const consistent = try cubeConsistentWith(allocator, background, kb, active, antecedent, null);
        if (consistent) {
            const can_fail = try cubeConsistentWith(allocator, background, kb, active, antecedent, consequent);
            return .{ .entailed = !can_fail, .level = level };
        }
        // At level > levels all finite-rank rules are inactive; only totally
        // exceptional rules (rank ∞) remain — final check happens at
        // level == ranking.levels since ranks ≥ levels only for ∞.
    }
    // Antecedent impossible even under background + fully exceptional core.
    return .{ .entailed = true, .level = null };
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

// Canon vocabulary: 0=bird, 1=fly, 2=penguin, 3=red.
const canon_kb = [_]Conditional{
    .{ .antecedent = &.{lp(0)}, .consequent = &.{lp(1)} }, // bird |~ fly
    .{ .antecedent = &.{lp(2)}, .consequent = &.{ln(1)} }, // penguin |~ ¬fly
    .{ .antecedent = &.{lp(2)}, .consequent = &.{lp(0)} }, // penguin |~ bird
};

test "klm: penguin canon ranks — bird 0, penguin rules 1" {
    var rk = try rank(testing.allocator, null, &canon_kb);
    defer rk.deinit();
    try testing.expectEqual(@as(u32, 2), rk.levels);
    try testing.expectEqual(@as(u32, 0), rk.ranks[0]);
    try testing.expectEqual(@as(u32, 1), rk.ranks[1]);
    try testing.expectEqual(@as(u32, 1), rk.ranks[2]);
}

test "klm: canonical queries — specificity, irrelevance, nonmonotonicity" {
    var rk = try rank(testing.allocator, null, &canon_kb);
    defer rk.deinit();
    const q = struct {
        fn run(rkp: *const Ranking, a: []const Lit, c: []const Lit) !bool {
            const res = try query(testing.allocator, null, &canon_kb, rkp, a, c);
            return res.entailed;
        }
    };
    // bird |~ fly
    try testing.expect(try q.run(&rk, &.{lp(0)}, &.{lp(1)}));
    // penguin |~ ¬fly (specificity beats bird-flies)
    try testing.expect(try q.run(&rk, &.{lp(2)}, &.{ln(1)}));
    // penguin |~/ fly
    try testing.expect(!try q.run(&rk, &.{lp(2)}, &.{lp(1)}));
    // penguin ∧ bird |~ ¬fly
    try testing.expect(try q.run(&rk, &.{ lp(2), lp(0) }, &.{ln(1)}));
    // red ∧ bird |~ fly (irrelevance preserved — the rational-closure signature)
    try testing.expect(try q.run(&rk, &.{ lp(3), lp(0) }, &.{lp(1)}));
    // penguin |~ bird
    try testing.expect(try q.run(&rk, &.{lp(2)}, &.{lp(0)}));
    // bird |~/ ¬fly
    try testing.expect(!try q.run(&rk, &.{lp(0)}, &.{ln(1)}));
}

test "klm: hard background makes antecedent impossible → vacuous + infinite rank" {
    var bg = Cnf.init(testing.allocator);
    defer bg.deinit();
    try bg.addClause(&.{ln(0)}); // ¬q hard
    const kb = [_]Conditional{
        .{ .antecedent = &.{lp(0)}, .consequent = &.{lp(1)} }, // q |~ x, q impossible
    };
    var rk = try rank(testing.allocator, &bg, &kb);
    defer rk.deinit();
    try testing.expectEqual(infinite_rank, rk.ranks[0]);
    const res = try query(testing.allocator, &bg, &kb, &rk, &.{lp(0)}, &.{ln(1)});
    try testing.expect(res.entailed);
    try testing.expect(res.level == null);
}

test "klm: empty KB entails only classical consequences of the antecedent" {
    const kb = [_]Conditional{};
    var rk = try rank(testing.allocator, null, &kb);
    defer rk.deinit();
    const yes = try query(testing.allocator, null, &kb, &rk, &.{ lp(0), lp(1) }, &.{lp(0)});
    try testing.expect(yes.entailed);
    const no = try query(testing.allocator, null, &kb, &rk, &.{lp(0)}, &.{lp(1)});
    try testing.expect(!no.entailed);
}
