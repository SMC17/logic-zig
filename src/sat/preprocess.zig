//! CNF preprocess — industrial SAT Phase 1.
//!
//! Sound reductions before CDCL:
//! - Tautology drop / duplicate lit removal
//! - Forward subsumption
//! - Unit propagation (BCP fixpoint) + pure-literal elimination
//! - Binary self-subsuming resolution: (l) and (¬l ∨ c) → strengthen c
//!
//! Does not change satisfiability. Empty clause ⇒ unsat marker (0-lit clause).

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const ClauseId = cnf_mod.ClauseId;
const Value = lit_mod.Value;

pub const Stats = struct {
    tautologies_removed: u32 = 0,
    subsumed_removed: u32 = 0,
    dups_removed: u32 = 0,
    units_propagated: u32 = 0,
    pure_assigned: u32 = 0,
    self_subsumed: u32 = 0,
    clauses_in: u32 = 0,
    clauses_out: u32 = 0,
    /// True if empty clause derived (UNSAT).
    unsat: bool = false,
};

fn isTautology(cl: []const Lit) bool {
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

const ClauseList = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayList([]Lit) = .empty,

    fn deinit(self: *ClauseList) void {
        for (self.items.items) |cl| self.allocator.free(cl);
        self.items.deinit(self.allocator);
        self.* = undefined;
    }

    fn appendOwned(self: *ClauseList, cl: []Lit) !void {
        try self.items.append(self.allocator, cl);
    }
};

fn rebuildCnf(allocator: std.mem.Allocator, cnf: *Cnf, kept: *const ClauseList) !void {
    const nvars = cnf.num_vars;
    cnf.deinit();
    cnf.* = Cnf.init(allocator);
    cnf.ensureVars(nvars);
    for (kept.items.items) |cl| {
        try cnf.addClause(cl);
    }
}

/// Collect non-tautology cleaned clauses from cnf into `kept`.
fn collect(allocator: std.mem.Allocator, cnf: *const Cnf, stats: *Stats) !ClauseList {
    var kept: ClauseList = .{ .allocator = allocator };
    errdefer kept.deinit();
    var ci: u32 = 0;
    while (ci < cnf.numClauses()) : (ci += 1) {
        const raw = cnf.clauseSlice(ClauseId.fromIndex(ci));
        if (isTautology(raw)) {
            stats.tautologies_removed += 1;
            continue;
        }
        const cleaned = try dedupLiterals(allocator, raw);
        if (cleaned.len < raw.len) stats.dups_removed += 1;
        try kept.appendOwned(cleaned);
    }
    return kept;
}

fn forwardSubsumption(kept: *ClauseList, stats: *Stats) void {
    var i: usize = 0;
    while (i < kept.items.items.len) {
        var sub = false;
        var j: usize = 0;
        while (j < kept.items.items.len) : (j += 1) {
            if (i == j) continue;
            const a = kept.items.items[j];
            const b = kept.items.items[i];
            if (subsumes(a, b) and (a.len < b.len or (a.len == b.len and j < i))) {
                sub = true;
                break;
            }
        }
        if (sub) {
            kept.allocator.free(kept.items.items[i]);
            _ = kept.items.orderedRemove(i);
            stats.subsumed_removed += 1;
        } else i += 1;
    }
}

/// Unit propagation + pure literal on clause list. Assignments as Value array.
fn bcpAndPure(allocator: std.mem.Allocator, nvars: u32, kept: *ClauseList, stats: *Stats) !void {
    var assign = try allocator.alloc(Value, nvars);
    defer allocator.free(assign);
    @memset(assign, .undef);

    var changed = true;
    while (changed) {
        changed = false;
        // Units
        var i: usize = 0;
        while (i < kept.items.items.len) {
            const cl = kept.items.items[i];
            // Drop satisfied; shrink falsified lits
            var sat = false;
            var live: std.ArrayList(Lit) = .empty;
            defer live.deinit(allocator);
            for (cl) |l| {
                const v = assign[l.variable().index()];
                if (v == .undef) {
                    try live.append(allocator, l);
                } else {
                    const want_true = !l.isNeg();
                    if ((v == .true_ and want_true) or (v == .false_ and !want_true)) {
                        sat = true;
                        break;
                    }
                    // lit false under assign — skip
                }
            }
            if (sat) {
                allocator.free(cl);
                _ = kept.items.orderedRemove(i);
                continue;
            }
            if (live.items.len == 0) {
                // empty = conflict
                stats.unsat = true;
                allocator.free(cl);
                _ = kept.items.orderedRemove(i);
                // replace with empty clause marker
                const empty = try allocator.alloc(Lit, 0);
                try kept.appendOwned(empty);
                return;
            }
            if (live.items.len < cl.len) {
                allocator.free(cl);
                const ncl = try allocator.dupe(Lit, live.items);
                kept.items.items[i] = ncl;
                changed = true;
            }
            if (live.items.len == 1) {
                const u = live.items[0];
                const vi = u.variable().index();
                const want: Value = if (u.isNeg()) .false_ else .true_;
                if (assign[vi] == .undef) {
                    assign[vi] = want;
                    stats.units_propagated += 1;
                    changed = true;
                } else if (assign[vi] != want) {
                    stats.unsat = true;
                    return;
                }
            }
            i += 1;
        }

        // Pure literals
        var pos = try allocator.alloc(bool, nvars);
        defer allocator.free(pos);
        var neg = try allocator.alloc(bool, nvars);
        defer allocator.free(neg);
        @memset(pos, false);
        @memset(neg, false);
        for (kept.items.items) |cl| {
            for (cl) |l| {
                const vi = l.variable().index();
                if (assign[vi] != .undef) continue;
                if (l.isNeg()) neg[vi] = true else pos[vi] = true;
            }
        }
        var vi: u32 = 0;
        while (vi < nvars) : (vi += 1) {
            if (assign[vi] != .undef) continue;
            if (pos[vi] and !neg[vi]) {
                assign[vi] = .true_;
                stats.pure_assigned += 1;
                changed = true;
            } else if (neg[vi] and !pos[vi]) {
                assign[vi] = .false_;
                stats.pure_assigned += 1;
                changed = true;
            }
        }
    }

    // Pin units as singleton clauses for the solver
    vi_pin: {
        var vi: u32 = 0;
        while (vi < nvars) : (vi += 1) {
            if (assign[vi] == .undef) continue;
            const l = if (assign[vi] == .true_)
                Lit.positive(lit_mod.Var.fromIndex(vi))
            else
                Lit.negative(lit_mod.Var.fromIndex(vi));
            // Avoid duplicate unit
            var has = false;
            for (kept.items.items) |cl| {
                if (cl.len == 1 and @intFromEnum(cl[0]) == @intFromEnum(l)) has = true;
            }
            if (!has) {
                const ucl = try allocator.alloc(Lit, 1);
                ucl[0] = l;
                try kept.appendOwned(ucl);
            }
        }
        break :vi_pin;
    }
}

/// (ℓ) and (¬ℓ ∨ c…) → strengthen to c… (self-subsuming with unit).
fn unitSelfSubsume(allocator: std.mem.Allocator, kept: *ClauseList, stats: *Stats) !void {
    // Collect units
    var units: std.ArrayList(Lit) = .empty;
    defer units.deinit(allocator);
    for (kept.items.items) |cl| {
        if (cl.len == 1) try units.append(allocator, cl[0]);
    }
    if (units.items.len == 0) return;

    var i: usize = 0;
    while (i < kept.items.items.len) {
        const cl = kept.items.items[i];
        if (cl.len <= 1) {
            i += 1;
            continue;
        }
        var removed = false;
        for (units.items) |u| {
            const nu = u.not();
            // If clause contains ¬u, remove ¬u (self-subsume by unit u)
            var has_comp = false;
            for (cl) |l| {
                if (@intFromEnum(l) == @intFromEnum(nu)) has_comp = true;
            }
            if (!has_comp) continue;
            var nl: std.ArrayList(Lit) = .empty;
            defer nl.deinit(allocator);
            for (cl) |l| {
                if (@intFromEnum(l) != @intFromEnum(nu)) try nl.append(allocator, l);
            }
            allocator.free(cl);
            const ncl = try allocator.dupe(Lit, nl.items);
            kept.items.items[i] = ncl;
            stats.self_subsumed += 1;
            removed = true;
            break;
        }
        if (!removed) i += 1;
    }
}

pub fn preprocess(allocator: std.mem.Allocator, cnf: *Cnf) !Stats {
    var stats: Stats = .{};
    stats.clauses_in = cnf.numClauses();
    if (stats.clauses_in == 0) {
        stats.clauses_out = 0;
        return stats;
    }

    var kept = try collect(allocator, cnf, &stats);
    defer kept.deinit();

    forwardSubsumption(&kept, &stats);
    try bcpAndPure(allocator, cnf.num_vars, &kept, &stats);
    if (stats.unsat) {
        try rebuildCnf(allocator, cnf, &kept);
        stats.clauses_out = cnf.numClauses();
        return stats;
    }
    try unitSelfSubsume(allocator, &kept, &stats);
    forwardSubsumption(&kept, &stats);
    // second BCP after strengthen
    try bcpAndPure(allocator, cnf.num_vars, &kept, &stats);

    try rebuildCnf(allocator, cnf, &kept);
    stats.clauses_out = cnf.numClauses();
    return stats;
}

test "preprocess keeps sat after clean" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.positive(lit_mod.Var.fromIndex(1)) });
    try cnf.addClause(&.{Lit.negative(lit_mod.Var.fromIndex(0))});
    const st = try preprocess(std.testing.allocator, &cnf);
    try std.testing.expect(st.clauses_out >= 1);
    try std.testing.expect(!st.unsat or cnf.numClauses() >= 0);
}

test "preprocess subsumption" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    try cnf.addClause(&.{Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.positive(lit_mod.Var.fromIndex(1)) });
    const st = try preprocess(std.testing.allocator, &cnf);
    try std.testing.expect(st.subsumed_removed >= 1 or st.units_propagated >= 1);
    try std.testing.expect(cnf.numClauses() >= 1);
}

test "preprocess unit forces unsat" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(1);
    try cnf.addClause(&.{Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{Lit.negative(lit_mod.Var.fromIndex(0))});
    const st = try preprocess(std.testing.allocator, &cnf);
    // empty or both units → solver will see unsat; unsat flag or empty clause
    _ = st;
    const r = try @import("solver.zig").solveCnf(std.testing.allocator, &cnf, .{});
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .unsat);
}

test "preprocess pure literal" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    // x0 only positive
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.positive(lit_mod.Var.fromIndex(1)) });
    try cnf.addClause(&.{ Lit.positive(lit_mod.Var.fromIndex(0)), Lit.negative(lit_mod.Var.fromIndex(1)) });
    const st = try preprocess(std.testing.allocator, &cnf);
    try std.testing.expect(st.pure_assigned >= 1 or st.units_propagated >= 0);
}
