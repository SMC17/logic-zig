//! Portfolio SAT: sequential multi-config probes (spin-off `logic-sat`).

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Value = lit_mod.Value;

pub const Result = struct {
    status: solver_mod.SolveStatus,
    conflicts: u64 = 0,
    config_index: u32 = 0,
    model: ?[]Value = null,
    learned: u64 = 0,
    config_name: []const u8 = "",
};

const Config = struct {
    opts: solver_mod.SolverOptions,
    name: []const u8,
};

fn configs() [4]Config {
    return .{
        .{ .name = "default", .opts = .{} },
        .{ .name = "fast-restart", .opts = .{ .restart_base = 50, .reduce_interval = 1000 } },
        .{ .name = "deep-learn", .opts = .{ .restart_base = 200, .reduce_keep_min = 300, .reduce_interval = 4000 } },
        .{ .name = "glue-heavy", .opts = .{ .reduce_by_lbd = true, .reduce_interval = 1200, .minimize = true } },
    };
}

pub fn solvePortfolio(
    allocator: std.mem.Allocator,
    formula: *const Cnf,
    total_conflicts: u64,
) !Result {
    const cfgs = configs();
    const per = @max(total_conflicts / cfgs.len, 10_000);
    var best_unknown: Result = .{ .status = .unknown };

    for (cfgs, 0..) |cfg, i| {
        var opts = cfg.opts;
        opts.max_conflicts = per;
        const r = try solver_mod.solveCnf(allocator, formula, opts);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .sat) {
            return .{
                .status = .sat,
                .conflicts = r.conflicts,
                .config_index = @intCast(i),
                .model = r.model,
                .learned = r.learned,
                .config_name = cfg.name,
            };
        }
        if (r.status == .unsat) {
            if (r.model) |m| allocator.free(m);
            return .{
                .status = .unsat,
                .conflicts = r.conflicts,
                .config_index = @intCast(i),
                .learned = r.learned,
                .config_name = cfg.name,
            };
        }
        if (r.model) |m| allocator.free(m);
        best_unknown.conflicts += r.conflicts;
        best_unknown.config_index = @intCast(i);
        best_unknown.config_name = cfg.name;
    }
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
    try std.testing.expect(r.status == .unsat);
}
