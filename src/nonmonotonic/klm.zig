//! KLM preferential / rational closure — ranked models + countermodels.
//!
//! Propositional conditional knowledge base of defaults φ ↝ ψ.
//! Rational closure ranks formulas by exceptionality (Pearl system Z).
//! Query α ↝ β is entailed at rank k if every minimal-rank model of α satisfies β.
//!
//! Fragment: finite propositional atoms ≤8, exhaustive ranking; countermodel
//! for non-entailment is an assignment at the decisive rank.

const std = @import("std");

pub const Default = struct {
    /// Bitmask of atoms required true in antecedent (simplified).
    ant_pos: u32,
    ant_neg: u32,
    cons_pos: u32,
    cons_neg: u32,
};

pub const Ranking = struct {
    /// rank[formula_index] = exceptionality rank (0 = most normal).
    ranks: []u32,
    max_rank: u32,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *Ranking) void {
        self.allocator.free(self.ranks);
        self.* = undefined;
    }
};

fn satisfies(world: u32, pos: u32, neg: u32) bool {
    return (world & pos) == pos and (world & neg) == 0;
}

fn satisfiesDefault(world: u32, d: Default) bool {
    if (!satisfies(world, d.ant_pos, d.ant_neg)) return true; // vacuously
    return satisfies(world, d.cons_pos, d.cons_neg);
}

/// System-Z style ranking: rank 0 = satisfied by some most-normal worlds.
pub fn rankDefaults(allocator: std.mem.Allocator, defs: []const Default, n_atoms: u32) !Ranking {
    if (n_atoms > 8) return error.TooManyAtoms;
    const full: u32 = if (n_atoms == 0) 0 else (@as(u32, 1) << @intCast(n_atoms)) - 1;
    var ranks = try allocator.alloc(u32, defs.len);
    @memset(ranks, 0);

    var remaining: std.ArrayList(usize) = .empty;
    defer remaining.deinit(allocator);
    for (defs, 0..) |_, i| try remaining.append(allocator, i);

    var current_rank: u32 = 0;
    while (remaining.items.len > 0 and current_rank < 64) : (current_rank += 1) {
        // Worlds that satisfy all still-remaining defaults
        var tolerated: std.ArrayList(usize) = .empty;
        defer tolerated.deinit(allocator);
        for (remaining.items) |di| {
            // exceptional if no world satisfying all remaining also satisfies ant of di?
            // simplified: materialization — default is tolerated if some world
            // models all remaining material implications and the antecedent.
            var ok = false;
            var w: u32 = 0;
            while (w <= full) : (w += 1) {
                var all = true;
                for (remaining.items) |dj| {
                    if (!satisfiesDefault(w, defs[dj])) {
                        all = false;
                        break;
                    }
                }
                if (all and satisfies(w, defs[di].ant_pos, defs[di].ant_neg)) {
                    ok = true;
                    break;
                }
            }
            if (ok) try tolerated.append(allocator, di);
        }
        if (tolerated.items.len == 0) {
            // all remaining get this rank and stop
            for (remaining.items) |di| ranks[di] = current_rank;
            break;
        }
        for (tolerated.items) |di| ranks[di] = current_rank;
        // remove tolerated from remaining
        var new_rem: std.ArrayList(usize) = .empty;
        for (remaining.items) |di| {
            var keep = true;
            for (tolerated.items) |t| {
                if (t == di) keep = false;
            }
            if (keep) try new_rem.append(allocator, di);
        }
        remaining.deinit(allocator);
        remaining = new_rem;
    }
    return .{ .ranks = ranks, .max_rank = current_rank, .allocator = allocator };
}

pub const QueryResult = struct {
    entailed: bool,
    decisive_rank: u32,
    /// Countermodel world bitmask when not entailed; undefined if entailed.
    countermodel: u32 = 0,
};

/// Query α ↝ β under rational closure (simplified materialization at min rank of α).
pub fn query(
    defs: []const Default,
    ranking: *const Ranking,
    ant_pos: u32,
    ant_neg: u32,
    cons_pos: u32,
    cons_neg: u32,
    n_atoms: u32,
) QueryResult {
    const full: u32 = if (n_atoms == 0) 0 else (@as(u32, 1) << @intCast(n_atoms)) - 1;
    // Min rank among worlds satisfying antecedent, respecting defaults by rank
    var best_rank: u32 = std.math.maxInt(u32);
    var w: u32 = 0;
    while (w <= full) : (w += 1) {
        if (!satisfies(w, ant_pos, ant_neg)) continue;
        // penalty = max rank of violated defaults
        var penalty: u32 = 0;
        for (defs, 0..) |d, i| {
            if (!satisfiesDefault(w, d)) penalty = @max(penalty, ranking.ranks[i] + 1);
        }
        if (penalty < best_rank) best_rank = penalty;
    }
    if (best_rank == std.math.maxInt(u32)) {
        return .{ .entailed = true, .decisive_rank = 0 }; // ant unsat
    }
    // Among worlds with that penalty, does each satisfy cons?
    w = 0;
    while (w <= full) : (w += 1) {
        if (!satisfies(w, ant_pos, ant_neg)) continue;
        var penalty: u32 = 0;
        for (defs, 0..) |d, i| {
            if (!satisfiesDefault(w, d)) penalty = @max(penalty, ranking.ranks[i] + 1);
        }
        if (penalty != best_rank) continue;
        if (!satisfies(w, cons_pos, cons_neg)) {
            return .{ .entailed = false, .decisive_rank = best_rank, .countermodel = w };
        }
    }
    return .{ .entailed = true, .decisive_rank = best_rank };
}

test "empty kb ranks" {
    var r = try rankDefaults(std.testing.allocator, &[_]Default{}, 2);
    defer r.deinit();
    try std.testing.expect(r.ranks.len == 0);
}

test "countermodel on failed query" {
    // Default: a ↝ b. Query a ↝ c should fail with countermodel a∧b∧¬c or similar
    const d = Default{ .ant_pos = 0b01, .ant_neg = 0, .cons_pos = 0b10, .cons_neg = 0 };
    var r = try rankDefaults(std.testing.allocator, &[_]Default{d}, 3);
    defer r.deinit();
    const q = query(&[_]Default{d}, &r, 0b01, 0, 0b100, 0, 3);
    try std.testing.expect(!q.entailed);
    // countermodel must satisfy ant a
    try std.testing.expect((q.countermodel & 0b01) != 0);
}
