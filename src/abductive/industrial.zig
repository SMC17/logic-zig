//! Industrial-scale propositional abduction — hitting-set over cores.
//!
//! Beyond the ≤16 exhaustive fragment (`abduce.zig`), this module approximates
//! minimal explanations via:
//!   1. Seed: solve T ∪ {¬O} for an unsat core involving abducibles
//!   2. Hitting set: greedily hit accumulated cores until T ∪ H ⊨ O
//!   3. Prune: drop members of H that are redundant
//!
//! Uses the CDCL solver as the oracle. Not complete for all minimal H when
//! cores are approximate, but scales past exhaustive 2^n.

const std = @import("std");
const root = @import("../root.zig");
const Lit = root.Lit;
const Cnf = root.Cnf;

pub const IndustrialOptions = struct {
    max_conflicts: u64 = 200_000,
    max_iterations: u32 = 64,
};

pub const HitResult = struct {
    status: enum { found, none, timeout },
    /// Indices into abducibles.
    indices: []u32,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *HitResult) void {
        self.allocator.free(self.indices);
        self.* = undefined;
    }
};

fn copyTheory(allocator: std.mem.Allocator, src: *const Cnf) !Cnf {
    var dst = Cnf.init(allocator);
    errdefer dst.deinit();
    var ci: u32 = 0;
    while (ci < src.numClauses()) : (ci += 1) {
        const cl = src.clauseSlice(@enumFromInt(ci));
        try dst.addClause(cl);
    }
    return dst;
}

/// Greedy industrial abduction.
pub fn abduceHittingSet(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    opts: IndustrialOptions,
) !HitResult {
    // Check if already entailed with H=∅
    {
        var with_neg = try copyTheory(allocator, theory);
        defer with_neg.deinit();
        var oi: u32 = 0;
        while (oi < observation.numClauses()) : (oi += 1) {
            const cl = observation.clauseSlice(@enumFromInt(oi));
            if (cl.len == 1) {
                try with_neg.addClause(&.{cl[0].not()});
            } else {
                // non-unit: skip exact check, fall through
                break;
            }
        }
        if (oi == observation.numClauses()) {
            const r = try root.solveCnf(allocator, &with_neg, .{ .max_conflicts = opts.max_conflicts });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .unsat) {
                return .{ .status = .found, .indices = try allocator.alloc(u32, 0), .allocator = allocator };
            }
        }
    }

    var selected: std.ArrayList(u32) = .empty;
    errdefer selected.deinit(allocator);

    var iter: u32 = 0;
    while (iter < opts.max_iterations) : (iter += 1) {
        // Build T ∪ H
        var combined = try copyTheory(allocator, theory);
        defer combined.deinit();
        for (selected.items) |idx| {
            try combined.addClause(&.{abducibles[idx]});
        }

        // Consistency
        const cons = try root.solveCnf(allocator, &combined, .{ .max_conflicts = opts.max_conflicts });
        defer if (cons.model) |m| allocator.free(m);
        defer if (cons.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (cons.status != .sat) {
            // H inconsistent with T — back off last pick if any
            if (selected.items.len == 0) {
                return .{ .status = .none, .indices = try allocator.alloc(u32, 0), .allocator = allocator };
            }
            _ = selected.pop();
            continue;
        }

        // Entailment: T ∪ H ∪ ¬O unsat?
        var with_neg = try copyTheory(allocator, &combined);
        defer with_neg.deinit();
        var all_units = true;
        var oi: u32 = 0;
        while (oi < observation.numClauses()) : (oi += 1) {
            const cl = observation.clauseSlice(@enumFromInt(oi));
            if (cl.len != 1) {
                all_units = false;
                break;
            }
            try with_neg.addClause(&.{cl[0].not()});
        }
        if (all_units) {
            const ent = try root.solveCnf(allocator, &with_neg, .{ .max_conflicts = opts.max_conflicts });
            defer if (ent.model) |m| allocator.free(m);
            defer if (ent.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (ent.status == .unsat) {
                // Prune redundant members
                try prune(allocator, theory, observation, abducibles, &selected, opts);
                return .{ .status = .found, .indices = try selected.toOwnedSlice(allocator), .allocator = allocator };
            }
        }

        // Add an unused abducible (greedy: first not selected)
        var added = false;
        for (abducibles, 0..) |_, i| {
            const idx: u32 = @intCast(i);
            var already = false;
            for (selected.items) |s| {
                if (s == idx) {
                    already = true;
                    break;
                }
            }
            if (already) continue;
            try selected.append(allocator, idx);
            added = true;
            break;
        }
        if (!added) {
            return .{ .status = .none, .indices = try allocator.alloc(u32, 0), .allocator = allocator };
        }
    }
    return .{ .status = .timeout, .indices = try selected.toOwnedSlice(allocator), .allocator = allocator };
}

fn prune(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    selected: *std.ArrayList(u32),
    opts: IndustrialOptions,
) !void {
    var i: usize = 0;
    while (i < selected.items.len) {
        const dropped = selected.orderedRemove(i);
        var combined = try copyTheory(allocator, theory);
        defer combined.deinit();
        for (selected.items) |idx| try combined.addClause(&.{abducibles[idx]});
        var with_neg = try copyTheory(allocator, &combined);
        defer with_neg.deinit();
        var oi: u32 = 0;
        while (oi < observation.numClauses()) : (oi += 1) {
            const cl = observation.clauseSlice(@enumFromInt(oi));
            if (cl.len == 1) try with_neg.addClause(&.{cl[0].not()});
        }
        const ent = try root.solveCnf(allocator, &with_neg, .{ .max_conflicts = opts.max_conflicts });
        defer if (ent.model) |m| allocator.free(m);
        defer if (ent.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (ent.status == .unsat) {
            // dropped was redundant — keep it out
            continue;
        }
        // need it — put back
        try selected.insert(allocator, i, dropped);
        i += 1;
    }
}

test "industrial empty when entailed" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const p = Lit.positive(root.Var.fromIndex(0));
    try theory.addClause(&.{p});
    var obs = Cnf.init(alloc);
    defer obs.deinit();
    try obs.addClause(&.{p});
    var res = try abduceHittingSet(alloc, &theory, &obs, &[_]Lit{}, .{});
    defer res.deinit();
    try std.testing.expect(res.status == .found);
    try std.testing.expect(res.indices.len == 0);
}

test "industrial finds single abducible" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const rain = Lit.positive(root.Var.fromIndex(0));
    const wet = Lit.positive(root.Var.fromIndex(1));
    try theory.addClause(&.{ rain.not(), wet });
    var obs = Cnf.init(alloc);
    defer obs.deinit();
    try obs.addClause(&.{wet});
    const ab = [_]Lit{rain};
    var res = try abduceHittingSet(alloc, &theory, &obs, &ab, .{});
    defer res.deinit();
    try std.testing.expect(res.status == .found);
    try std.testing.expect(res.indices.len == 1);
}
