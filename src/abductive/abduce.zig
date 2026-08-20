//! Propositional abduction — inference to the best (minimal) explanation.
//!
//! Given theory T, observation O, and a pool of abducible candidates A,
//! find a subset-minimal H ⊆ A such that:
//!   1. T ∪ H ⊨ O
//!   2. T ∪ H is consistent
//!
//! Fragment: exhaustive search over subsets of small abducible sets (≤16),
//! using the existing CDCL solver as the entailment oracle. This is the
//! correct small-domain engine; industrial-scale abduction (hitting-set /
//! iterative MUS) is a later depth pass.

const std = @import("std");
const root = @import("../root.zig");
const Lit = root.Lit;
const Var = root.Var;
const Cnf = root.Cnf;

pub const AbduceOptions = struct {
    /// Prefer cardinality-minimal explanations when multiple subset-minima exist.
    prefer_cardinality: bool = true,
    max_conflicts: u64 = 100_000,
};

pub const Explanation = struct {
    /// Indices into the abducibles slice that form H.
    indices: []u32,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *Explanation) void {
        self.allocator.free(self.indices);
        self.* = undefined;
    }
};

pub const AbduceResult = struct {
    status: enum { found, none, timeout },
    explanation: ?Explanation = null,

    pub fn deinit(self: *AbduceResult) void {
        if (self.explanation) |*e| e.deinit();
        self.* = undefined;
    }
};

/// Solve propositional abduction.
///
/// - `theory`: CNF encoding of background knowledge T
/// - `observation`: CNF encoding of O (usually unit clauses)
/// - `abducibles`: candidate hypothesis literals
///
/// Returns a subset-minimal set of abducible indices, or `.none` if no explanation exists.
pub fn abduce(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    opts: AbduceOptions,
) !AbduceResult {
    if (abducibles.len > 16) {
        // Fragment guard: exhaustive 2^n is intentional for the small-domain engine.
        return error.TooManyAbducibles;
    }

    const n = abducibles.len;
    const full_mask: u32 = if (n == 0) 0 else (@as(u32, 1) << @intCast(n)) - 1;

    var best_mask: ?u32 = null;
    var best_card: u32 = std.math.maxInt(u32);

    var mask: u32 = 0;
    while (mask <= full_mask) : (mask += 1) {
        // Build T ∪ H
        var combined = Cnf.init(allocator);
        defer combined.deinit();

        for (0..theory.numClauses()) |ci| {
            const cl = theory.clauseSlice(@enumFromInt(@as(u32, @intCast(ci))));
            try combined.addClause(cl);
        }
        var card: u32 = 0;
        var bit: u32 = 0;
        while (bit < n) : (bit += 1) {
            if ((mask & (@as(u32, 1) << @intCast(bit))) != 0) {
                try combined.addClause(&.{abducibles[bit]});
                card += 1;
            }
        }

        // Consistency: T ∪ H must be sat
        const cons = try root.solveCnf(allocator, &combined, .{ .max_conflicts = opts.max_conflicts });
        defer if (cons.model) |m| allocator.free(m);
        defer if (cons.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (cons.status != .sat) continue;

        // Entailment check
        var obs_units_only = true;
        for (0..observation.numClauses()) |ci| {
            const cl = observation.clauseSlice(@enumFromInt(@as(u32, @intCast(ci))));
            if (cl.len != 1) {
                obs_units_only = false;
                break;
            }
        }

        if (!obs_units_only) {
            // Sound model check for non-unit observations
            if (cons.model) |model| {
                if (!observation.checkModel(model)) continue;
            } else continue;
        } else {
            // Exact: T ∪ H ∪ {¬l for each unit l in O} must be unsat
            var with_neg = Cnf.init(allocator);
            defer with_neg.deinit();
            for (0..combined.numClauses()) |ci| {
                const cl = combined.clauseSlice(@enumFromInt(@as(u32, @intCast(ci))));
                try with_neg.addClause(cl);
            }
            for (0..observation.numClauses()) |ci| {
                const cl = observation.clauseSlice(@enumFromInt(@as(u32, @intCast(ci))));
                try with_neg.addClause(&.{cl[0].not()});
            }
            const ent = try root.solveCnf(allocator, &with_neg, .{ .max_conflicts = opts.max_conflicts });
            defer if (ent.model) |m| allocator.free(m);
            defer if (ent.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (ent.status != .unsat) continue;
        }

        // H is a valid explanation. Track minimal.
        if (best_mask) |bm| {
            if ((mask & bm) == bm and mask != bm) continue;
        }
        if (opts.prefer_cardinality) {
            if (card < best_card) {
                best_card = card;
                best_mask = mask;
            }
        } else {
            if (best_mask == null) best_mask = mask;
        }
    }

    if (best_mask) |bm| {
        var indices: std.ArrayList(u32) = .empty;
        errdefer indices.deinit(allocator);
        var bit: u32 = 0;
        while (bit < n) : (bit += 1) {
            if ((bm & (@as(u32, 1) << @intCast(bit))) != 0) {
                try indices.append(allocator, bit);
            }
        }
        return .{
            .status = .found,
            .explanation = .{
                .indices = try indices.toOwnedSlice(allocator),
                .allocator = allocator,
            },
        };
    }
    return .{ .status = .none };
}

/// Convenience: abduce from a single observation literal.
pub fn abduceUnit(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation_lit: Lit,
    abducibles: []const Lit,
    opts: AbduceOptions,
) !AbduceResult {
    var obs = Cnf.init(allocator);
    defer obs.deinit();
    try obs.addClause(&.{observation_lit});
    return abduce(allocator, theory, &obs, abducibles, opts);
}

test "abduce classic rain-wet" {
    // T: rain → wet   (¬rain ∨ wet)
    // O: wet
    // A: {rain, sprinkler}
    // Minimal H = {rain}
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const rain = Lit.positive(Var.fromIndex(0));
    const wet = Lit.positive(Var.fromIndex(1));
    const sprinkler = Lit.positive(Var.fromIndex(2));
    try theory.addClause(&.{ rain.not(), wet });

    const abducibles = [_]Lit{ rain, sprinkler };
    var result = try abduceUnit(alloc, &theory, wet, &abducibles, .{});
    defer result.deinit();
    try std.testing.expect(result.status == .found);
    const exp = result.explanation.?;
    try std.testing.expect(exp.indices.len == 1);
    try std.testing.expect(exp.indices[0] == 0); // rain
}

test "abduce none when inconsistent" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try theory.addClause(&.{a.not()});
    const abducibles = [_]Lit{a};
    var result = try abduceUnit(alloc, &theory, a, &abducibles, .{});
    defer result.deinit();
    try std.testing.expect(result.status == .none);
}

test "abduce empty abducibles with entailed observation" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const p = Lit.positive(Var.fromIndex(0));
    try theory.addClause(&.{p});
    var result = try abduceUnit(alloc, &theory, p, &[_]Lit{}, .{});
    defer result.deinit();
    try std.testing.expect(result.status == .found);
    try std.testing.expect(result.explanation.?.indices.len == 0);
}
