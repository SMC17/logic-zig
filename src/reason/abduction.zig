//! Propositional abduction — Peircean explanatory inference as an engine.
//!
//! Problem: given background theory B (CNF), observation O (cube of literals)
//! and a set of abducible literals A, find hypotheses H ⊆ A with
//!
//!   B ∧ H ⊨ O    (checked as: B ∧ H ∧ ¬O is UNSAT)
//!   B ∧ H ⊭ ⊥    (checked as: B ∧ H is SAT)
//!
//! and H **subset-minimal**: no proper subset of H entails O.
//!
//! Enumeration is MARCO-style over the abducible power set: a map solver
//! proposes unexplored subsets; UNSAT seeds shrink to a deletion-minimal MUS
//! of the assumptions (a candidate explanation, minimality inherited from
//! `Solver.solveAssumptions`); SAT seeds grow to an MSS. Both prune the map.
//! Candidate explanations inconsistent with B are discarded but stay blocked.
//!
//! Deduction is the oracle throughout — every abductive answer is a pair of
//! SAT calls away from its certificate.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const maxsat = @import("../sat/maxsat.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Solver = solver_mod.Solver;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const Status = enum {
    /// Enumeration ran; see `complete` for exhaustiveness.
    ok,
    /// B itself is UNSAT — every H "explains" everything; no honest answer.
    inconsistent_background,
};

pub const Options = struct {
    /// Stop after this many explanations (completeness flag stays false).
    max_explanations: u32 = 64,
    /// Hard cap on map-solver iterations.
    max_iterations: u32 = 4096,
};

pub const Result = struct {
    allocator: std.mem.Allocator,
    status: Status = .ok,
    /// Subset-minimal, background-consistent explanations (owned slices of
    /// abducible literals, sorted by DIMACS value). When
    /// `entailed_without_hypothesis`, contains the single empty explanation.
    explanations: std.ArrayList([]Lit) = .empty,
    /// B ⊨ O already — the unique minimal explanation is ∅.
    entailed_without_hypothesis: bool = false,
    /// Every subset-minimal explanation was enumerated (map exhausted).
    complete: bool = false,

    pub fn deinit(self: *Result) void {
        for (self.explanations.items) |e| self.allocator.free(e);
        self.explanations.deinit(self.allocator);
        self.* = undefined;
    }
};

fn cloneCnf(allocator: std.mem.Allocator, src: *const Cnf) !Cnf {
    var out = Cnf.init(allocator);
    errdefer out.deinit();
    out.ensureVars(src.num_vars);
    for (0..src.numClauses()) |ci| {
        try out.addClause(src.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    return out;
}

pub fn abduce(
    allocator: std.mem.Allocator,
    background: *const Cnf,
    observation: []const Lit,
    abducibles: []const Lit,
    opts: Options,
) !Result {
    var result = Result{ .allocator = allocator };
    errdefer result.deinit();

    // Working theory: B ∧ ¬O. ¬O of a cube is a single clause.
    var work = try cloneCnf(allocator, background);
    defer work.deinit();
    for (observation) |l| work.ensureVars(l.variable().index() + 1);
    for (abducibles) |l| work.ensureVars(l.variable().index() + 1);
    {
        var neg_obs: std.ArrayList(Lit) = .empty;
        defer neg_obs.deinit(allocator);
        for (observation) |l| try neg_obs.append(allocator, l.not());
        try work.addClause(neg_obs.items);
    }

    var back = try cloneCnf(allocator, background);
    defer back.deinit();
    back.ensureVars(work.num_vars);

    var main = try Solver.init(allocator, &work, .{});
    defer main.deinit();
    var cons = try Solver.init(allocator, &back, .{});
    defer cons.deinit();

    // B consistent at all?
    {
        const r = try cons.solveAssumptions(&.{});
        defer if (r.model) |m| allocator.free(m);
        if (r.status != .sat) {
            result.status = .inconsistent_background;
            return result;
        }
    }
    // B ⊨ O with the empty hypothesis?
    {
        const r = try main.solveAssumptions(&.{});
        defer if (r.model) |m| allocator.free(m);
        if (r.status == .unsat) {
            result.entailed_without_hypothesis = true;
            result.complete = true;
            try result.explanations.append(allocator, try allocator.alloc(Lit, 0));
            return result;
        }
    }
    // Entailment is monotone in H: if the full abducible set fails, all fail.
    {
        const r = try main.solveAssumptions(abducibles);
        defer if (r.model) |m| allocator.free(m);
        defer if (r.assumption_core) |c| allocator.free(c);
        if (r.status == .sat) {
            result.complete = true;
            return result;
        }
    }

    const m: u32 = @intCast(abducibles.len);
    var map_cnf = Cnf.init(allocator);
    defer map_cnf.deinit();
    map_cnf.ensureVars(m);
    var map = try Solver.init(allocator, &map_cnf, .{});
    defer map.deinit();
    // Bias seeds toward maximal subsets (fewer grow steps; correctness unaffected).
    for (map.phase) |*p| p.* = true;

    var seed: std.ArrayList(u32) = .empty;
    defer seed.deinit(allocator);
    var seed_lits: std.ArrayList(Lit) = .empty;
    defer seed_lits.deinit(allocator);
    var block: std.ArrayList(Lit) = .empty;
    defer block.deinit(allocator);

    var iter: u32 = 0;
    while (iter < opts.max_iterations) : (iter += 1) {
        const mr = try map.solveAssumptions(&.{});
        defer if (mr.model) |mm| allocator.free(mm);
        if (mr.status != .sat) {
            result.complete = true;
            return result;
        }
        const model = mr.model.?;
        seed.clearRetainingCapacity();
        seed_lits.clearRetainingCapacity();
        for (0..m) |i| {
            if (model[i] == .true_) {
                try seed.append(allocator, @intCast(i));
                try seed_lits.append(allocator, abducibles[i]);
            }
        }

        const sr = try main.solveAssumptions(seed_lits.items);
        defer if (sr.model) |mm| allocator.free(mm);
        defer if (sr.assumption_core) |c| allocator.free(c);

        if (sr.status == .sat) {
            // Grow seed to an MSS, then block all its subsets.
            var in_mss = try allocator.alloc(bool, m);
            defer allocator.free(in_mss);
            @memset(in_mss, false);
            for (seed.items) |i| in_mss[i] = true;
            for (0..m) |i| {
                if (in_mss[i]) continue;
                try seed_lits.append(allocator, abducibles[i]);
                const gr = try main.solveAssumptions(seed_lits.items);
                defer if (gr.model) |mm| allocator.free(mm);
                defer if (gr.assumption_core) |c| allocator.free(c);
                if (gr.status == .sat) {
                    in_mss[i] = true;
                } else {
                    _ = seed_lits.pop();
                }
            }
            block.clearRetainingCapacity();
            for (0..m) |i| {
                if (!in_mss[i]) try block.append(allocator, Lit.positive(Var.fromIndex(@intCast(i))));
            }
            if (block.items.len == 0) {
                // MSS is the full set — every subset is covered.
                result.complete = true;
                return result;
            }
            try map.addClausePermanent(block.items);
        } else {
            // Deletion-minimal MUS of the assumptions = subset-minimal candidate.
            const core = sr.assumption_core orelse {
                // Empty seed went UNSAT — contradicts the entailment pre-check.
                return result;
            };
            var h: std.ArrayList(Lit) = .empty;
            defer h.deinit(allocator);
            block.clearRetainingCapacity();
            for (core) |d| {
                const l = Lit.fromDimacs(d);
                try h.append(allocator, l);
                // Map the literal back to its abducible index for blocking.
                for (abducibles, 0..) |a, i| {
                    if (a == l) {
                        try block.append(allocator, Lit.negative(Var.fromIndex(@intCast(i))));
                        break;
                    }
                }
            }
            const cr = try cons.solveAssumptions(h.items);
            defer if (cr.model) |mm| allocator.free(mm);
            defer if (cr.assumption_core) |c| allocator.free(c);
            if (cr.status == .sat) {
                const owned = try allocator.dupe(Lit, h.items);
                std.mem.sort(Lit, owned, {}, litLess);
                try result.explanations.append(allocator, owned);
            }
            if (block.items.len == 0) return result; // defensive; unreachable
            try map.addClausePermanent(block.items);
            if (result.explanations.items.len >= opts.max_explanations) return result;
        }
    }
    return result;
}

fn litLess(_: void, a: Lit, b: Lit) bool {
    const ad = a.toDimacs();
    const bd = b.toDimacs();
    const aa = @abs(ad);
    const ab = @abs(bd);
    if (aa != ab) return aa < ab;
    return ad < bd;
}

// ── Cost-ranked abduction ────────────────────────────────────────────

pub const CostOptions = struct {
    /// Per-abducible weights (parallel to `abducibles`); empty → all 1,
    /// i.e. cardinality-minimal. Zero weights are allowed but mean the
    /// optimum may include cost-free abducibles.
    weights: []const u32 = &.{},
    /// Hitting-set refinement rounds before giving up.
    max_rounds: u32 = 1024,
};

pub const MinCostResult = struct {
    allocator: std.mem.Allocator,
    status: Status = .ok,
    /// Cost-optimal valid explanation (entails O, consistent with B), or null
    /// when none exists / not found within rounds. Owned, sorted by DIMACS.
    explanation: ?[]Lit = null,
    cost: u64 = 0,
    /// Optimum proven: every hitting-set probe solved to MaxSAT optimality
    /// and the returned candidate closed the duality gap.
    optimal: bool = false,
    entailed_without_hypothesis: bool = false,

    pub fn deinit(self: *MinCostResult) void {
        if (self.explanation) |e| self.allocator.free(e);
        self.* = undefined;
    }
};

/// Minimum-cost abduction via the implicit hitting-set duality:
/// H entails O iff H hits every MCS (complement of a maximal non-entailing
/// subset). Iterate: min-cost hitting set of known MCSes (MaxSAT) → if the
/// candidate entails and is consistent it is cost-optimal (the hitting-set
/// optimum lower-bounds every valid explanation); if it fails entailment,
/// grow it to an MSS and record the new MCS; if it entails but is
/// inconsistent with B, block that exact set and continue.
pub fn abduceMinCost(
    allocator: std.mem.Allocator,
    background: *const Cnf,
    observation: []const Lit,
    abducibles: []const Lit,
    opts: CostOptions,
) !MinCostResult {
    std.debug.assert(opts.weights.len == 0 or opts.weights.len == abducibles.len);
    var result = MinCostResult{ .allocator = allocator };
    errdefer result.deinit();

    var work = try cloneCnf(allocator, background);
    defer work.deinit();
    for (observation) |l| work.ensureVars(l.variable().index() + 1);
    for (abducibles) |l| work.ensureVars(l.variable().index() + 1);
    {
        var neg_obs: std.ArrayList(Lit) = .empty;
        defer neg_obs.deinit(allocator);
        for (observation) |l| try neg_obs.append(allocator, l.not());
        try work.addClause(neg_obs.items);
    }
    var back = try cloneCnf(allocator, background);
    defer back.deinit();
    back.ensureVars(work.num_vars);

    var main = try Solver.init(allocator, &work, .{});
    defer main.deinit();
    var cons = try Solver.init(allocator, &back, .{});
    defer cons.deinit();

    {
        const r = try cons.solveAssumptions(&.{});
        defer if (r.model) |m| allocator.free(m);
        if (r.status != .sat) {
            result.status = .inconsistent_background;
            return result;
        }
    }
    {
        const r = try main.solveAssumptions(&.{});
        defer if (r.model) |m| allocator.free(m);
        if (r.status == .unsat) {
            result.entailed_without_hypothesis = true;
            result.optimal = true;
            result.explanation = try allocator.alloc(Lit, 0);
            return result;
        }
    }
    {
        const r = try main.solveAssumptions(abducibles);
        defer if (r.model) |m| allocator.free(m);
        defer if (r.assumption_core) |c| allocator.free(c);
        if (r.status == .sat) {
            result.optimal = true; // provably no explanation at any cost
            return result;
        }
    }

    const m: u32 = @intCast(abducibles.len);
    // Hitting-set side: selector var i ⇔ abducible i chosen.
    var hs_hard = Cnf.init(allocator);
    defer hs_hard.deinit();
    hs_hard.ensureVars(m);
    var soft = try allocator.alloc(maxsat.SoftClause, m);
    defer allocator.free(soft);
    var soft_lits = try allocator.alloc([1]Lit, m);
    defer allocator.free(soft_lits);
    for (0..m) |i| {
        soft_lits[i] = .{Lit.negative(Var.fromIndex(@intCast(i)))};
        soft[i] = .{
            .lits = &soft_lits[i],
            .weight = if (opts.weights.len > 0) opts.weights[i] else 1,
        };
    }

    var cand_lits: std.ArrayList(Lit) = .empty;
    defer cand_lits.deinit(allocator);
    var block: std.ArrayList(Lit) = .empty;
    defer block.deinit(allocator);
    var all_probes_optimal = true;

    var round: u32 = 0;
    while (round < opts.max_rounds) : (round += 1) {
        var hs = try maxsat.solve(allocator, &hs_hard, soft, .{});
        defer hs.deinit();
        if (hs.status == .unsat_hard) return result; // every subset blocked
        if (hs.status != .optimal) all_probes_optimal = false;
        const model = hs.model orelse return result;

        cand_lits.clearRetainingCapacity();
        var in_cand = try allocator.alloc(bool, m);
        defer allocator.free(in_cand);
        @memset(in_cand, false);
        for (0..m) |i| {
            if (model[i] == .true_) {
                in_cand[i] = true;
                try cand_lits.append(allocator, abducibles[i]);
            }
        }

        const er = try main.solveAssumptions(cand_lits.items);
        defer if (er.model) |mm| allocator.free(mm);
        defer if (er.assumption_core) |c| allocator.free(c);

        if (er.status == .unsat) {
            const cr = try cons.solveAssumptions(cand_lits.items);
            defer if (cr.model) |mm| allocator.free(mm);
            defer if (cr.assumption_core) |c| allocator.free(c);
            if (cr.status == .sat) {
                const owned = try allocator.dupe(Lit, cand_lits.items);
                std.mem.sort(Lit, owned, {}, litLess);
                result.explanation = owned;
                result.cost = hs.cost;
                result.optimal = all_probes_optimal;
                return result;
            }
            // Entailing but inconsistent: block exactly this set.
            block.clearRetainingCapacity();
            for (0..m) |i| {
                const v = Var.fromIndex(@intCast(i));
                try block.append(allocator, if (in_cand[i]) Lit.negative(v) else Lit.positive(v));
            }
            try hs_hard.addClause(block.items);
        } else {
            // Not entailing: grow to MSS, record its complement as a new MCS.
            for (0..m) |i| {
                if (in_cand[i]) continue;
                try cand_lits.append(allocator, abducibles[i]);
                const gr = try main.solveAssumptions(cand_lits.items);
                defer if (gr.model) |mm| allocator.free(mm);
                defer if (gr.assumption_core) |c| allocator.free(c);
                if (gr.status == .sat) {
                    in_cand[i] = true;
                } else {
                    _ = cand_lits.pop();
                }
            }
            block.clearRetainingCapacity();
            for (0..m) |i| {
                if (!in_cand[i]) try block.append(allocator, Lit.positive(Var.fromIndex(@intCast(i))));
            }
            std.debug.assert(block.items.len > 0); // full set entails (pre-checked)
            try hs_hard.addClause(block.items);
        }
    }
    return result;
}

/// Deductive certificate for one explanation: B ∧ H ⊨ O and B ∧ H is SAT.
/// The re-check uses fresh solvers, so it is independent of enumeration state.
pub fn verifyExplanation(
    allocator: std.mem.Allocator,
    background: *const Cnf,
    observation: []const Lit,
    explanation: []const Lit,
) !bool {
    var work = try cloneCnf(allocator, background);
    defer work.deinit();
    for (observation) |l| work.ensureVars(l.variable().index() + 1);
    for (explanation) |l| work.ensureVars(l.variable().index() + 1);
    {
        var neg_obs: std.ArrayList(Lit) = .empty;
        defer neg_obs.deinit(allocator);
        for (observation) |l| try neg_obs.append(allocator, l.not());
        try work.addClause(neg_obs.items);
    }
    var s = try Solver.init(allocator, &work, .{});
    defer s.deinit();
    {
        const r = try s.solveAssumptions(explanation);
        defer if (r.model) |m| allocator.free(m);
        defer if (r.assumption_core) |c| allocator.free(c);
        if (r.status != .unsat) return false;
    }
    var back = try cloneCnf(allocator, background);
    defer back.deinit();
    for (explanation) |l| back.ensureVars(l.variable().index() + 1);
    var cs = try Solver.init(allocator, &back, .{});
    defer cs.deinit();
    const r = try cs.solveAssumptions(explanation);
    defer if (r.model) |m| allocator.free(m);
    defer if (r.assumption_core) |c| allocator.free(c);
    return r.status == .sat;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn lp(v: u32) Lit {
    return Lit.positive(Var.fromIndex(v));
}
fn ln(v: u32) Lit {
    return Lit.negative(Var.fromIndex(v));
}

/// Diagnosis fixture: 0=faultA, 1=faultB, 2=symptom1, 3=symptom2.
/// faultA → s1, faultB → s1, faultB → s2.
fn diagnosisTheory(allocator: std.mem.Allocator) !Cnf {
    var b = Cnf.init(allocator);
    errdefer b.deinit();
    try b.addClause(&.{ ln(0), lp(2) });
    try b.addClause(&.{ ln(1), lp(2) });
    try b.addClause(&.{ ln(1), lp(3) });
    return b;
}

test "abduce: two singleton explanations for one symptom" {
    var b = try diagnosisTheory(testing.allocator);
    defer b.deinit();
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{ lp(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.status == .ok);
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 2), r.explanations.items.len);
    for (r.explanations.items) |e| {
        try testing.expectEqual(@as(usize, 1), e.len);
        try testing.expect(e[0] == lp(0) or e[0] == lp(1));
        try testing.expect(try verifyExplanation(testing.allocator, &b, &.{lp(2)}, e));
    }
    try testing.expect(r.explanations.items[0][0] != r.explanations.items[1][0]);
}

test "abduce: conjunction observation forces the stronger cause" {
    var b = try diagnosisTheory(testing.allocator);
    defer b.deinit();
    var r = try abduce(testing.allocator, &b, &.{ lp(2), lp(3) }, &.{ lp(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expectEqual(@as(usize, 1), r.explanations.items[0].len);
    try testing.expect(r.explanations.items[0][0] == lp(1));
}

test "abduce: inconsistent hypothesis is rejected" {
    var b = try diagnosisTheory(testing.allocator);
    defer b.deinit();
    // Rule out faultA in the background: {¬faultA}.
    try b.addClause(&.{ln(0)});
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{ lp(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expect(r.explanations.items[0][0] == lp(1));
}

test "abduce: minimality — superset never returned" {
    // 0=a, 1=b, 2=o with a→o. {a} explains; {a,b} must not be returned.
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(2) });
    b.ensureVars(2);
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{ lp(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expectEqual(@as(usize, 1), r.explanations.items[0].len);
    try testing.expect(r.explanations.items[0][0] == lp(0));
}

test "abduce: joint cause needs both abducibles" {
    // a ∧ b → o encoded as {¬a, ¬b, o}; only {a,b} explains o.
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), ln(1), lp(2) });
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{ lp(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expectEqual(@as(usize, 2), r.explanations.items[0].len);
    try testing.expect(try verifyExplanation(testing.allocator, &b, &.{lp(2)}, r.explanations.items[0]));
    // Falsifier probe: each proper subset must fail entailment.
    for (r.explanations.items[0]) |l| {
        try testing.expect(!try verifyExplanation(testing.allocator, &b, &.{lp(2)}, &.{l}));
    }
}

test "abduce: already entailed → empty explanation" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{lp(2)});
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{lp(0)}, .{});
    defer r.deinit();
    try testing.expect(r.entailed_without_hypothesis);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expectEqual(@as(usize, 0), r.explanations.items[0].len);
}

test "abduce: no explanation when abducibles cannot reach observation" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(2) });
    b.ensureVars(4);
    // Only abducible is unrelated var 3.
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{lp(3)}, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 0), r.explanations.items.len);
}

test "abduce: inconsistent background reported" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{lp(0)});
    try b.addClause(&.{ln(0)});
    var r = try abduce(testing.allocator, &b, &.{lp(1)}, &.{lp(2)}, .{});
    defer r.deinit();
    try testing.expect(r.status == .inconsistent_background);
}

/// Test oracle: brute-force min-cost valid explanation over the power set.
fn bruteMinCost(
    allocator: std.mem.Allocator,
    background: *const Cnf,
    observation: []const Lit,
    abducibles: []const Lit,
    weights: []const u32,
) !?u64 {
    var best: ?u64 = null;
    const total: u32 = @as(u32, 1) << @intCast(abducibles.len);
    var subset: std.ArrayList(Lit) = .empty;
    defer subset.deinit(allocator);
    var mask: u32 = 0;
    while (mask < total) : (mask += 1) {
        subset.clearRetainingCapacity();
        var cost: u64 = 0;
        for (abducibles, 0..) |a, i| {
            if ((mask >> @intCast(i)) & 1 == 1) {
                try subset.append(allocator, a);
                cost += if (weights.len > 0) weights[i] else 1;
            }
        }
        if (best != null and cost >= best.?) continue;
        if (try verifyExplanation(allocator, background, observation, subset.items)) {
            best = cost;
        }
    }
    return best;
}

test "abduce min-cost: weighted picks the cheap pair over the pricey singleton" {
    // a→o and b∧c→o; w(a)=5, w(b)=w(c)=1 → optimum {b,c} cost 2.
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(3) });
    try b.addClause(&.{ ln(1), ln(2), lp(3) });
    const abds = [_]Lit{ lp(0), lp(1), lp(2) };
    const w = [_]u32{ 5, 1, 1 };
    var r = try abduceMinCost(testing.allocator, &b, &.{lp(3)}, &abds, .{ .weights = &w });
    defer r.deinit();
    try testing.expect(r.optimal);
    try testing.expectEqual(@as(u64, 2), r.cost);
    try testing.expectEqual(@as(usize, 2), r.explanation.?.len);
    try testing.expect(r.explanation.?[0] == lp(1) and r.explanation.?[1] == lp(2));
    const brute = try bruteMinCost(testing.allocator, &b, &.{lp(3)}, &abds, &w);
    try testing.expectEqual(brute.?, r.cost);
}

test "abduce min-cost: cardinality default picks the singleton" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(3) });
    try b.addClause(&.{ ln(1), ln(2), lp(3) });
    const abds = [_]Lit{ lp(0), lp(1), lp(2) };
    var r = try abduceMinCost(testing.allocator, &b, &.{lp(3)}, &abds, .{});
    defer r.deinit();
    try testing.expect(r.optimal);
    try testing.expectEqual(@as(u64, 1), r.cost);
    try testing.expect(r.explanation.?[0] == lp(0));
}

test "abduce min-cost: inconsistent cheapest is skipped for the next valid" {
    // a→o but ¬a in B; b→o. w(a)=1, w(b)=3 → {a} entails but inconsistent → {b}.
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(2) });
    try b.addClause(&.{ln(0)});
    try b.addClause(&.{ ln(1), lp(2) });
    const abds = [_]Lit{ lp(0), lp(1) };
    const w = [_]u32{ 1, 3 };
    var r = try abduceMinCost(testing.allocator, &b, &.{lp(2)}, &abds, .{ .weights = &w });
    defer r.deinit();
    try testing.expect(r.optimal);
    try testing.expectEqual(@as(u64, 3), r.cost);
    try testing.expect(r.explanation.?[0] == lp(1));
    const brute = try bruteMinCost(testing.allocator, &b, &.{lp(2)}, &abds, &w);
    try testing.expectEqual(brute.?, r.cost);
}

test "abduce min-cost: entailed already → empty at cost 0" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{lp(1)});
    var r = try abduceMinCost(testing.allocator, &b, &.{lp(1)}, &.{lp(0)}, .{});
    defer r.deinit();
    try testing.expect(r.entailed_without_hypothesis);
    try testing.expect(r.optimal);
    try testing.expectEqual(@as(u64, 0), r.cost);
    try testing.expectEqual(@as(usize, 0), r.explanation.?.len);
}

test "abduce min-cost: no explanation reachable" {
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(0), lp(2) });
    b.ensureVars(4);
    var r = try abduceMinCost(testing.allocator, &b, &.{lp(2)}, &.{lp(3)}, .{});
    defer r.deinit();
    try testing.expect(r.optimal);
    try testing.expect(r.explanation == null);
}

test "abduce min-cost: random instances match brute force" {
    var prng = std.Random.DefaultPrng.init(0xABDCE);
    const rand = prng.random();
    var instance: u32 = 0;
    while (instance < 25) : (instance += 1) {
        // Vars 0..3 abducible, 4..5 intermediate, obs var 5.
        var b = Cnf.init(testing.allocator);
        defer b.deinit();
        b.ensureVars(6);
        const n_cl = 2 + rand.uintLessThan(u32, 5);
        var cbuf: [3]Lit = undefined;
        for (0..n_cl) |_| {
            const len = 2 + rand.uintLessThan(u32, 2);
            for (0..len - 1) |i| {
                const v = rand.uintLessThan(u32, 5);
                cbuf[i] = if (rand.uintLessThan(u32, 4) == 0) lp(v) else ln(v);
            }
            cbuf[len - 1] = if (rand.boolean()) lp(4 + rand.uintLessThan(u32, 2)) else lp(rand.uintLessThan(u32, 6));
            try b.addClause(cbuf[0..len]);
        }
        const abds = [_]Lit{ lp(0), lp(1), lp(2), lp(3) };
        var w: [4]u32 = undefined;
        for (0..4) |i| w[i] = 1 + rand.uintLessThan(u32, 5);
        var r = try abduceMinCost(testing.allocator, &b, &.{lp(5)}, &abds, .{ .weights = &w });
        defer r.deinit();
        if (r.status == .inconsistent_background) continue;
        const brute = try bruteMinCost(testing.allocator, &b, &.{lp(5)}, &abds, &w);
        if (brute) |opt| {
            try testing.expect(r.explanation != null);
            try testing.expect(r.optimal);
            try testing.expectEqual(opt, r.cost);
            try testing.expect(try verifyExplanation(testing.allocator, &b, &.{lp(5)}, r.explanation.?));
        } else {
            try testing.expect(r.explanation == null);
        }
    }
}

test "abduce: negative abducible literals" {
    // ¬a → o encoded {a, o}; abducibles {¬a, b}. Explanation {¬a}.
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ lp(0), lp(2) });
    b.ensureVars(2);
    var r = try abduce(testing.allocator, &b, &.{lp(2)}, &.{ ln(0), lp(1) }, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.explanations.items.len);
    try testing.expect(r.explanations.items[0][0] == ln(0));
}
