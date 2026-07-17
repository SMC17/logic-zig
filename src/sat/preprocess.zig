//! CNF preprocess — industrial SAT Phase 1 foundation.
//!
//! Cheap, sound reductions before CDCL:
//! - Drop tautologies (p ∨ ¬p ∨ …)
//! - Forward subsumption (remove clauses strictly weaker than another)
//! - Duplicate literal removal
//!
//! Does not change satisfiability. Optional; enabled by default in `api.v1.satCnf`.

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const ClauseId = cnf_mod.ClauseId;

pub const Stats = struct {
    tautologies_removed: u32 = 0,
    subsumed_removed: u32 = 0,
    dups_removed: u32 = 0,
    clauses_in: u32 = 0,
    clauses_out: u32 = 0,
};

fn litKey(l: Lit) u32 {
    return @intFromEnum(l);
}

fn isTautology(cl: []const Lit) bool {
    // O(n²) fine for preprocess on moderate clauses
    var i: usize = 0;
    while (i < cl.len) : (i += 1) {
        var j = i + 1;
        while (j < cl.len) : (j += 1) {
            if (cl[i].variable().index() == cl[j].variable().index() and cl[i].isNeg() != cl[j].isNeg())
                return true;
        }
    }
    return false;
}

fn dedupLiterals(allocator: std.mem.Allocator, cl: []const Lit) ![]Lit {
    var out: std.ArrayList(Lit) = .empty;
    errdefer out.deinit(allocator);
    for (cl) |l| {
        var found = false;
        for (out.items) |o| {
            if (@intFromEnum(o) == @intFromEnum(l)) {
                found = true;
                break;
            }
        }
        if (!found) try out.append(allocator, l);
    }
    return try out.toOwnedSlice(allocator);
}

/// Returns true if `a` subsumes `b` (every lit of a appears in b).
fn subsumes(a: []const Lit, b: []const Lit) bool {
    if (a.len > b.len) return false;
    for (a) |la| {
        var ok = false;
        for (b) |lb| {
            if (@intFromEnum(la) == @intFromEnum(lb)) {
                ok = true;
                break;
            }
        }
        if (!ok) return false;
    }
    return true;
}

/// In-place-ish rebuild: allocate new Cnf content via replace.
pub fn preprocess(allocator: std.mem.Allocator, cnf: *Cnf) !Stats {
    var stats: Stats = .{};
    stats.clauses_in = cnf.numClauses();

    // Collect cleaned clauses
    var kept: std.ArrayList([]Lit) = .empty;
    defer {
        for (kept.items) |cl| allocator.free(cl);
        kept.deinit(allocator);
    }

    var ci: u32 = 0;
    while (ci < cnf.numClauses()) : (ci += 1) {
        const raw = cnf.clauseSlice(ClauseId.fromIndex(ci));
        if (isTautology(raw)) {
            stats.tautologies_removed += 1;
            continue;
        }
        const cleaned = try dedupLiterals(allocator, raw);
        if (cleaned.len < raw.len) stats.dups_removed += 1;
        if (cleaned.len == 0) {
            // empty clause — keep as unsat marker
            try kept.append(allocator, cleaned);
            continue;
        }
        try kept.append(allocator, cleaned);
    }

    // Forward subsumption: drop b if some a⊂b
    var i: usize = 0;
    while (i < kept.items.len) {
        var sub = false;
        var j: usize = 0;
        while (j < kept.items.len) : (j += 1) {
            if (i == j) continue;
            if (subsumes(kept.items[j], kept.items[i]) and kept.items[j].len < kept.items[i].len) {
                sub = true;
                break;
            }
            // equal-length equal content: drop duplicate clause
            if (kept.items[j].len == kept.items[i].len and j < i and subsumes(kept.items[j], kept.items[i])) {
                sub = true;
                break;
            }
        }
        if (sub) {
            allocator.free(kept.items[i]);
            _ = kept.orderedRemove(i);
            stats.subsumed_removed += 1;
        } else {
            i += 1;
        }
    }

    // Rebuild CNF clause DB
    const nvars = cnf.num_vars;
    cnf.deinit();
    cnf.* = Cnf.init(allocator);
    cnf.ensureVars(nvars);
    for (kept.items) |cl| {
        try cnf.addClause(cl);
    }
    stats.clauses_out = cnf.numClauses();
    return stats;
}

test "preprocess keeps sat after clean" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    // Cnf.addClause already drops tautologies; preprocess still sound on normal clauses
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.positive(lit_mod.Var.fromIndex(1)) });
    try cnf.addClause(&.{ Lit.negative(lit_mod.Var.fromIndex(0)) });
    const st = try preprocess(std.testing.allocator, &cnf);
    try std.testing.expect(st.clauses_out >= 1);
    try std.testing.expect(cnf.numClauses() >= 1);
}

test "preprocess subsumption" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    // (1) subsumes (1 ∨ 2)
    try cnf.addClause(&.{Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.positive(lit_mod.Var.fromIndex(1)) });
    const st = try preprocess(std.testing.allocator, &cnf);
    try std.testing.expect(st.subsumed_removed >= 1);
    try std.testing.expect(cnf.numClauses() == 1);
}
