//! Portfolio SAT: sequential multi-config probes with model validation & stats.
//! Flagship: `logic-sat portfolio`.

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const lit_mod = @import("../core/lit.zig");
const drat_mod = @import("drat.zig");

const Cnf = cnf_mod.Cnf;
const Value = lit_mod.Value;

pub const Result = struct {
    status: solver_mod.SolveStatus,
    conflicts: u64 = 0,
    config_index: u32 = 0,
    model: ?[]Value = null,
    learned: u64 = 0,
    config_name: []const u8 = "",
    configs_tried: u32 = 0,
    /// When proof requested and UNSAT.
    proof: ?drat_mod.Proof = null,
    model_valid: bool = true,
};

pub const PortfolioOptions = struct {
    total_conflicts: u64 = 2_000_000,
    /// Share budget unevenly: first configs get less (fast probes).
    ramp: bool = true,
    proof_on_unsat: bool = false,
    validate_model: bool = true,
};

const Config = struct {
    opts: solver_mod.SolverOptions,
    name: []const u8,
};

fn configs() [6]Config {
    return .{
        .{ .name = "default", .opts = .{} },
        .{ .name = "fast-restart", .opts = .{ .restart_base = 50, .reduce_interval = 1000, .minimize = true } },
        .{ .name = "luby-tight", .opts = .{ .restart_base = 32, .reduce_interval = 800, .reduce_keep_min = 80 } },
        .{ .name = "deep-learn", .opts = .{ .restart_base = 200, .reduce_keep_min = 400, .reduce_interval = 4000 } },
        .{ .name = "glue-heavy", .opts = .{ .reduce_by_lbd = true, .reduce_interval = 1200, .minimize = true, .reduce_keep_min = 250 } },
        .{ .name = "patient", .opts = .{ .restart_base = 300, .reduce_interval = 6000, .minimize = true } },
    };
}

fn budgetFor(i: usize, n: usize, total: u64, ramp: bool) u64 {
    if (!ramp) return @max(total / n, 5_000);
    // Early configs: smaller slices; later: larger residual.
    // Weights: 1,1,2,2,3,3 roughly
    const weights = [_]u64{ 1, 1, 2, 2, 3, 3 };
    var sum: u64 = 0;
    var w: u64 = 0;
    var k: usize = 0;
    while (k < n) : (k += 1) {
        const wi = if (k < weights.len) weights[k] else 2;
        sum += wi;
        if (k == i) w = wi;
    }
    return @max((total * w) / sum, 5_000);
}

pub fn solvePortfolio(
    allocator: std.mem.Allocator,
    formula: *const Cnf,
    total_conflicts: u64,
) !Result {
    return solvePortfolioOpts(allocator, formula, .{ .total_conflicts = total_conflicts });
}

pub fn solvePortfolioOpts(
    allocator: std.mem.Allocator,
    formula: *const Cnf,
    popts: PortfolioOptions,
) !Result {
    const cfgs = configs();
    var best_unknown: Result = .{ .status = .unknown };
    var tried: u32 = 0;

    for (cfgs, 0..) |cfg, i| {
        var opts = cfg.opts;
        opts.max_conflicts = budgetFor(i, cfgs.len, popts.total_conflicts, popts.ramp);
        // Only last config (or proof_on_unsat) enables proof to save time
        opts.proof = popts.proof_on_unsat and (i + 1 == cfgs.len or true);
        if (popts.proof_on_unsat) opts.proof = true;

        const r = try solver_mod.solveCnf(allocator, formula, opts);
        tried += 1;
        best_unknown.conflicts += r.conflicts;
        best_unknown.configs_tried = tried;

        if (r.status == .sat) {
            var model_valid = true;
            if (popts.validate_model) {
                if (r.model) |m| {
                    model_valid = formula.checkModel(m);
                    if (!model_valid) {
                        // discard and try next config
                        allocator.free(m);
                        if (r.proof) |*p| {
                            var pp = p.*;
                            pp.deinit();
                        }
                        continue;
                    }
                }
            }
            if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            }
            return .{
                .status = .sat,
                .conflicts = r.conflicts,
                .config_index = @intCast(i),
                .model = r.model,
                .learned = r.learned,
                .config_name = cfg.name,
                .configs_tried = tried,
                .model_valid = model_valid,
            };
        }
        if (r.status == .unsat) {
            if (r.model) |m| allocator.free(m);
            // Verify internal RUP if proof present
            if (r.proof) |*pf| {
                const ok = try pf.verifyRup(allocator, formula);
                if (!ok) {
                    var pp = pf.*;
                    pp.deinit();
                    // treat as unknown for this config, continue
                    continue;
                }
                return .{
                    .status = .unsat,
                    .conflicts = r.conflicts,
                    .config_index = @intCast(i),
                    .learned = r.learned,
                    .config_name = cfg.name,
                    .configs_tried = tried,
                    .proof = pf.*,
                };
            }
            return .{
                .status = .unsat,
                .conflicts = r.conflicts,
                .config_index = @intCast(i),
                .learned = r.learned,
                .config_name = cfg.name,
                .configs_tried = tried,
            };
        }
        if (r.model) |m| allocator.free(m);
        if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        }
        best_unknown.config_index = @intCast(i);
        best_unknown.config_name = cfg.name;
    }
    best_unknown.configs_tried = tried;
    return best_unknown;
}

test "portfolio solves unit unsat" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(1);
    try cnf.addClause(&.{lit_mod.Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{lit_mod.Lit.negative(lit_mod.Var.fromIndex(0))});
    const r = try solvePortfolio(std.testing.allocator, &cnf, 100_000);
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .unsat);
    try std.testing.expect(r.configs_tried >= 1);
}

test "portfolio sat model validates" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    try cnf.addClause(&.{ lit_mod.Lit.positive(lit_mod.Var.fromIndex(0)), lit_mod.Lit.positive(lit_mod.Var.fromIndex(1)) });
    const r = try solvePortfolioOpts(std.testing.allocator, &cnf, .{ .total_conflicts = 50_000, .validate_model = true });
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .sat);
    try std.testing.expect(r.model_valid);
    try std.testing.expect(r.model != null);
    try std.testing.expect(cnf.checkModel(r.model.?));
}

test "portfolio proof on unsat verifies rup" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(1);
    try cnf.addClause(&.{lit_mod.Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{lit_mod.Lit.negative(lit_mod.Var.fromIndex(0))});
    var r = try solvePortfolioOpts(std.testing.allocator, &cnf, .{
        .total_conflicts = 100_000,
        .proof_on_unsat = true,
    });
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .unsat);
    try std.testing.expect(r.proof != null);
}
