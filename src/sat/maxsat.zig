//! Weighted partial MaxSAT over the CDCL core.
//!
//! Hard clauses must hold; each soft clause carries a weight paid when
//! falsified. Exact optimum by descending upper-bound search: relax each soft
//! clause with a selector, then repeatedly ask "is there a model with total
//! relaxed weight ≤ cost−1?" using a sequential weighted counter (SWC)
//! pseudo-Boolean encoding. UNSAT at bound cost−1 certifies optimality.
//!
//! Scope: exact on the scales logic-zig cares about (explanation ranking,
//! small optimization queries) — no claim of industrial MaxSAT parity.

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const SoftClause = struct {
    lits: []const Lit,
    weight: u32,
};

pub const Status = enum {
    /// Optimum proven (UNSAT at cost−1).
    optimal,
    /// Best model found within budget; optimality not proven.
    satisfiable,
    /// Hard clauses alone are UNSAT.
    unsat_hard,
    /// Budget exhausted before any model.
    unknown,
};

pub const Options = struct {
    max_conflicts_per_probe: u64 = 1_000_000,
};

pub const Result = struct {
    allocator: std.mem.Allocator,
    status: Status,
    /// Total weight of falsified soft clauses under `model`.
    cost: u64 = 0,
    /// Best model over original vars (length = original num_vars), if any.
    model: ?[]Value = null,

    pub fn deinit(self: *Result) void {
        if (self.model) |m| self.allocator.free(m);
        self.* = undefined;
    }
};

fn softCost(model: []const Value, soft: []const SoftClause) u64 {
    var cost: u64 = 0;
    for (soft) |sc| {
        var satisfied = false;
        for (sc.lits) |l| {
            const v = model[l.variable().index()];
            const lit_true = if (l.isNeg()) v == .false_ else v == .true_;
            if (lit_true) {
                satisfied = true;
                break;
            }
        }
        if (!satisfied) cost += sc.weight;
    }
    return cost;
}

/// Sequential weighted counter: clauses enforcing Σ w_i·sel_i ≤ bound.
/// R(i,j) ⇔ "sum of first i+1 selectors ≥ j+1" (one-sided, sufficient for ≤).
fn encodeAtMost(
    out: *Cnf,
    selectors: []const Lit,
    weights: []const u32,
    bound: u64,
    aux_base: u32,
) !void {
    const n: u32 = @intCast(selectors.len);
    if (n == 0) return;
    const k: u32 = @intCast(@min(bound, std.math.maxInt(u32)));

    // Selector too heavy on its own → forced off.
    for (selectors, weights) |s, w| {
        if (w > k) try out.addClause(&.{s.not()});
    }
    if (k == 0) return;

    const reg = struct {
        fn lit(base: u32, kk: u32, i: u32, j: u32) Lit {
            return Lit.positive(Var.fromIndex(base + i * kk + j));
        }
    };
    out.ensureVars(aux_base + n * k);

    for (0..n) |i_us| {
        const i: u32 = @intCast(i_us);
        const w = weights[i];
        for (0..k) |j_us| {
            const j: u32 = @intCast(j_us);
            // Carry: R(i-1,j) → R(i,j)
            if (i > 0) {
                try out.addClause(&.{ reg.lit(aux_base, k, i - 1, j).not(), reg.lit(aux_base, k, i, j) });
            }
            // Own weight: sel_i → R(i,j) for j+1 ≤ w
            if (w > k) continue; // already forced off
            if (j + 1 <= w) {
                try out.addClause(&.{ selectors[i].not(), reg.lit(aux_base, k, i, j) });
            }
            // Add: sel_i ∧ R(i-1,j) → R(i, j+w)
            if (i > 0 and j + 1 + w <= k) {
                try out.addClause(&.{
                    selectors[i].not(),
                    reg.lit(aux_base, k, i - 1, j).not(),
                    reg.lit(aux_base, k, i, j + w),
                });
            }
        }
        // Overflow: sel_i ∧ R(i-1, k−w) → sum > k, forbidden.
        if (i > 0 and w <= k and w >= 1) {
            const j_over: u32 = k - w; // R index for value k−w+1
            try out.addClause(&.{ selectors[i].not(), reg.lit(aux_base, k, i - 1, j_over).not() });
        }
    }
}

pub fn solve(
    allocator: std.mem.Allocator,
    hard: *const Cnf,
    soft: []const SoftClause,
    opts: Options,
) !Result {
    var num_vars: u32 = hard.num_vars;
    for (soft) |sc| {
        for (sc.lits) |l| num_vars = @max(num_vars, l.variable().index() + 1);
    }

    // Relaxed base: hard ∧ (soft_i ∨ sel_i). Selector vars follow originals.
    var base = Cnf.init(allocator);
    defer base.deinit();
    base.ensureVars(num_vars + @as(u32, @intCast(soft.len)));
    for (0..hard.numClauses()) |ci| {
        try base.addClause(hard.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    var selectors = try allocator.alloc(Lit, soft.len);
    defer allocator.free(selectors);
    var weights = try allocator.alloc(u32, soft.len);
    defer allocator.free(weights);
    var buf: std.ArrayList(Lit) = .empty;
    defer buf.deinit(allocator);
    for (soft, 0..) |sc, i| {
        selectors[i] = Lit.positive(Var.fromIndex(num_vars + @as(u32, @intCast(i))));
        weights[i] = sc.weight;
        buf.clearRetainingCapacity();
        try buf.appendSlice(allocator, sc.lits);
        try buf.append(allocator, selectors[i]);
        try base.addClause(buf.items);
    }
    const aux_base = num_vars + @as(u32, @intCast(soft.len));

    // Initial model (no bound).
    var best_model: ?[]Value = null;
    errdefer if (best_model) |m| allocator.free(m);
    var best_cost: u64 = 0;
    {
        const r = try solver_mod.solveCnf(allocator, &base, .{
            .max_conflicts = opts.max_conflicts_per_probe,
        });
        defer if (r.model) |m| allocator.free(m);
        switch (r.status) {
            .unsat => return .{ .allocator = allocator, .status = .unsat_hard },
            .unknown => return .{ .allocator = allocator, .status = .unknown },
            .sat => {
                best_cost = softCost(r.model.?, soft);
                best_model = try allocator.dupe(Value, r.model.?[0..num_vars]);
            },
        }
    }

    // Descend: probe bound = best_cost − 1 until UNSAT (optimum) or budget.
    var proven = best_cost == 0;
    while (best_cost > 0) {
        var probe = Cnf.init(allocator);
        defer probe.deinit();
        probe.ensureVars(base.num_vars);
        for (0..base.numClauses()) |ci| {
            try probe.addClause(base.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
        }
        try encodeAtMost(&probe, selectors, weights, best_cost - 1, aux_base);
        const r = try solver_mod.solveCnf(allocator, &probe, .{
            .max_conflicts = opts.max_conflicts_per_probe,
        });
        defer if (r.model) |m| allocator.free(m);
        switch (r.status) {
            .unsat => {
                proven = true;
                break;
            },
            .unknown => break,
            .sat => {
                const c = softCost(r.model.?, soft);
                std.debug.assert(c < best_cost);
                allocator.free(best_model.?);
                best_model = try allocator.dupe(Value, r.model.?[0..num_vars]);
                best_cost = c;
            },
        }
    }

    return .{
        .allocator = allocator,
        // Cost 0 is trivially optimal — no cheaper total exists.
        .status = if (proven or best_cost == 0) .optimal else .satisfiable,
        .cost = best_cost,
        .model = best_model,
    };
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn lp(v: u32) Lit {
    return Lit.positive(Var.fromIndex(v));
}
fn ln(v: u32) Lit {
    return Lit.negative(Var.fromIndex(v));
}

/// Brute-force optimum over all assignments (test oracle).
fn bruteForce(hard: *const Cnf, soft: []const SoftClause, num_vars: u32) ?u64 {
    var best: ?u64 = null;
    const total: u64 = @as(u64, 1) << @intCast(num_vars);
    var assign: [16]Value = undefined;
    var a: u64 = 0;
    while (a < total) : (a += 1) {
        for (0..num_vars) |v| {
            assign[v] = if ((a >> @intCast(v)) & 1 == 1) .true_ else .false_;
        }
        var hard_ok = true;
        for (0..hard.numClauses()) |ci| {
            const cl = hard.clauseSlice(ClauseId.fromIndex(@intCast(ci)));
            var sat = false;
            for (cl) |l| {
                const val = assign[l.variable().index()];
                if (if (l.isNeg()) val == .false_ else val == .true_) {
                    sat = true;
                    break;
                }
            }
            if (!sat) {
                hard_ok = false;
                break;
            }
        }
        if (!hard_ok) continue;
        const c = softCost(assign[0..num_vars], soft);
        if (best == null or c < best.?) best = c;
    }
    return best;
}

test "maxsat: prefers cheap violation" {
    // Hard: x0 ∨ x1. Soft: ¬x0 (w=3), ¬x1 (w=1) → set x1, pay 1.
    var hard = Cnf.init(testing.allocator);
    defer hard.deinit();
    try hard.addClause(&.{ lp(0), lp(1) });
    const soft = [_]SoftClause{
        .{ .lits = &.{ln(0)}, .weight = 3 },
        .{ .lits = &.{ln(1)}, .weight = 1 },
    };
    var r = try solve(testing.allocator, &hard, &soft, .{});
    defer r.deinit();
    try testing.expect(r.status == .optimal);
    try testing.expectEqual(@as(u64, 1), r.cost);
}

test "maxsat: all soft satisfiable → cost 0" {
    var hard = Cnf.init(testing.allocator);
    defer hard.deinit();
    hard.ensureVars(2);
    const soft = [_]SoftClause{
        .{ .lits = &.{lp(0)}, .weight = 5 },
        .{ .lits = &.{lp(1)}, .weight = 7 },
    };
    var r = try solve(testing.allocator, &hard, &soft, .{});
    defer r.deinit();
    try testing.expect(r.status == .optimal);
    try testing.expectEqual(@as(u64, 0), r.cost);
}

test "maxsat: hard unsat detected" {
    var hard = Cnf.init(testing.allocator);
    defer hard.deinit();
    try hard.addClause(&.{lp(0)});
    try hard.addClause(&.{ln(0)});
    var r = try solve(testing.allocator, &hard, &soft_none, .{});
    defer r.deinit();
    try testing.expect(r.status == .unsat_hard);
}
const soft_none = [_]SoftClause{};

test "maxsat: contradictory units pay the lighter side" {
    // Soft: x0 (w=2), ¬x0 (w=5) → keep x0 true, pay 2.
    var hard = Cnf.init(testing.allocator);
    defer hard.deinit();
    hard.ensureVars(1);
    const soft = [_]SoftClause{
        .{ .lits = &.{lp(0)}, .weight = 2 },
        .{ .lits = &.{ln(0)}, .weight = 5 },
    };
    var r = try solve(testing.allocator, &hard, &soft, .{});
    defer r.deinit();
    try testing.expect(r.status == .optimal);
    try testing.expectEqual(@as(u64, 2), r.cost);
}

test "maxsat: random instances match brute force" {
    var prng = std.Random.DefaultPrng.init(0xC0FFEE);
    const rand = prng.random();
    var checked: u32 = 0;
    var instance: u32 = 0;
    while (instance < 60) : (instance += 1) {
        const nv = 3 + rand.uintLessThan(u32, 5); // 3..7 vars
        var hard = Cnf.init(testing.allocator);
        defer hard.deinit();
        hard.ensureVars(nv);
        const n_hard = rand.uintLessThan(u32, 5);
        var cbuf: [3]Lit = undefined;
        for (0..n_hard) |_| {
            const len = 1 + rand.uintLessThan(u32, 3);
            for (0..len) |i| {
                const v = rand.uintLessThan(u32, nv);
                cbuf[i] = if (rand.boolean()) lp(v) else ln(v);
            }
            try hard.addClause(cbuf[0..len]);
        }
        var soft_lits: [8][2]Lit = undefined;
        var soft: [8]SoftClause = undefined;
        const n_soft = 2 + rand.uintLessThan(u32, 7); // 2..8
        for (0..n_soft) |i| {
            const len = 1 + rand.uintLessThan(u32, 2);
            for (0..len) |j| {
                const v = rand.uintLessThan(u32, nv);
                soft_lits[i][j] = if (rand.boolean()) lp(v) else ln(v);
            }
            soft[i] = .{ .lits = soft_lits[i][0..len], .weight = 1 + rand.uintLessThan(u32, 5) };
        }
        var r = try solve(testing.allocator, &hard, soft[0..n_soft], .{});
        defer r.deinit();
        const expect = bruteForce(&hard, soft[0..n_soft], nv);
        if (expect) |opt| {
            if (r.status != .optimal or r.cost != opt) {
                std.debug.print("\nmaxsat mismatch inst={d} nv={d} status={s} got={d} want={d}\n", .{
                    instance, nv, @tagName(r.status), r.cost, opt,
                });
                for (0..hard.numClauses()) |ci| {
                    std.debug.print("  hard:", .{});
                    for (hard.clauseSlice(ClauseId.fromIndex(@intCast(ci)))) |l| std.debug.print(" {d}", .{l.toDimacs()});
                    std.debug.print("\n", .{});
                }
                for (soft[0..n_soft]) |sc| {
                    std.debug.print("  soft w={d}:", .{sc.weight});
                    for (sc.lits) |l| std.debug.print(" {d}", .{l.toDimacs()});
                    std.debug.print("\n", .{});
                }
            }
            try testing.expect(r.status == .optimal);
            try testing.expectEqual(opt, r.cost);
            checked += 1;
        } else {
            try testing.expect(r.status == .unsat_hard);
        }
    }
    try testing.expect(checked >= 30); // most random instances have sat hard part
}
