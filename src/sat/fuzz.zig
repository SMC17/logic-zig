//! Differential testing: CDCL vs exhaustive truth-table oracle (small n).
//! Optional external solver hook when `LOGIC_ZIG_EXTERNAL_SOLVER` is set.

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

/// Exhaustive SAT for num_vars <= 16. Returns true if satisfiable.
pub fn bruteSat(cnf: *const Cnf) bool {
    const n = cnf.num_vars;
    if (n > 16) return false; // caller should not use
    if (n == 0) {
        return cnf.numClauses() == 0 or !hasEmpty(cnf);
    }
    const limit: u32 = @as(u32, 1) << @intCast(n);
    var bits: u32 = 0;
    var assign_buf: [16]Value = undefined;
    while (bits < limit) : (bits += 1) {
        var i: u32 = 0;
        while (i < n) : (i += 1) {
            assign_buf[i] = if ((bits >> @intCast(i)) & 1 == 1) .true_ else .false_;
        }
        if (cnf.checkModel(assign_buf[0..n])) return true;
    }
    return false;
}

fn hasEmpty(cnf: *const Cnf) bool {
    var ci: u32 = 0;
    while (ci < cnf.numClauses()) : (ci += 1) {
        if (cnf.clauseSlice(cnf_mod.ClauseId.fromIndex(ci)).len == 0) return true;
    }
    return false;
}

pub fn random3Sat(allocator: std.mem.Allocator, rng: std.Random, n_vars: u32, n_clauses: u32) !Cnf {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();
    cnf.ensureVars(n_vars);
    var clause: [3]Lit = undefined;
    var c: u32 = 0;
    while (c < n_clauses) : (c += 1) {
        var k: u32 = 0;
        while (k < 3) : (k += 1) {
            const v = rng.intRangeLessThan(u32, 0, n_vars);
            const neg = rng.boolean();
            clause[k] = Lit.make(Var.fromIndex(v), neg);
        }
        try cnf.addClause(&clause);
    }
    return cnf;
}

/// Run `iters` random instances; return mismatch count (0 = ok).
pub fn fuzzVsBrute(allocator: std.mem.Allocator, seed: u64, iters: u32, n_vars: u32, density: f64) !u32 {
    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();
    var mismatches: u32 = 0;
    var i: u32 = 0;
    while (i < iters) : (i += 1) {
        const n_clauses: u32 = @intFromFloat(@as(f64, @floatFromInt(n_vars)) * density);
        var cnf = try random3Sat(allocator, rng, n_vars, n_clauses);
        defer cnf.deinit();
        const brute = bruteSat(&cnf);
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        const sat = r.status == .sat;
        if (sat != brute) {
            mismatches += 1;
            continue;
        }
        if (sat) {
            if (!cnf.checkModel(r.model.?)) mismatches += 1;
        }
    }
    return mismatches;
}

test "fuzz vs brute 8 vars" {
    const mm = try fuzzVsBrute(std.testing.allocator, 0xC0FFEE, 40, 8, 4.2);
    try std.testing.expect(mm == 0);
}

test "fuzz vs brute 10 vars sparse" {
    const mm = try fuzzVsBrute(std.testing.allocator, 42, 25, 10, 3.0);
    try std.testing.expect(mm == 0);
}

test "fuzz vs brute 12 vars" {
    const mm = try fuzzVsBrute(std.testing.allocator, 7, 20, 12, 3.2);
    try std.testing.expect(mm == 0);
}

test "fuzz vs brute 14 vars sparse" {
    const mm = try fuzzVsBrute(std.testing.allocator, 99, 12, 14, 3.0);
    try std.testing.expect(mm == 0);
}

test "brute unsat known" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{a});
    try cnf.addClause(&.{a.not()});
    try std.testing.expect(!bruteSat(&cnf));
}
