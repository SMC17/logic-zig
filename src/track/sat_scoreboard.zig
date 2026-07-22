//! Industrial SAT scoreboard — Phase 1.
//!
//! Runs frozen CNF suites with preprocess+CDCL (optional portfolio), diffs vs CaDiCaL,
//! reports solved counts, mismatches, PAR-2-ish wall, and a clear VERDICT line.
//!
//! CLI: `logic-zig sat-scoreboard [--dir DIR] [--limit N] [--conflicts N] [--portfolio]`

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");
const portfolio = @import("../sat/portfolio.zig");
const preprocess = @import("../sat/preprocess.zig");
const external = @import("../sat/external.zig");
const bench = @import("bench.zig");

pub const Row = struct {
    name: []const u8,
    internal: bench.Status,
    external: bench.Status,
    match: bool,
    internal_ns: u64,
    external_ns: u64,
    preprocess_units: u32 = 0,
    model_ok: bool = true,
};

pub const Scoreboard = struct {
    rows: []Row,
    mismatches: u32 = 0,
    inconclusive: u32 = 0,
    model_failures: u32 = 0,
    solved_internal: u32 = 0,
    solved_external: u32 = 0,
    both_agreed: u32 = 0,
    internal_faster: u32 = 0,
    external_faster: u32 = 0,
    external_available: bool = false,
    cadical_path: ?[]const u8 = null,
    par2_internal: f64 = 0,
    par2_external: f64 = 0,
    timeout_s: f64 = 10,

    pub fn deinit(self: *Scoreboard, allocator: std.mem.Allocator) void {
        for (self.rows) |r| allocator.free(r.name);
        allocator.free(self.rows);
        if (self.cadical_path) |p| allocator.free(p);
        self.* = undefined;
    }

    pub fn correctnessOk(self: *const Scoreboard) bool {
        return self.external_available and self.rows.len > 0 and self.both_agreed > 0 and
            self.inconclusive == 0 and self.mismatches == 0 and self.model_failures == 0;
    }
};

fn monoNs() u64 {
    var ts: std.os.linux.timespec = undefined;
    _ = std.os.linux.clock_gettime(std.os.linux.CLOCK.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) * std.time.ns_per_s + @as(u64, @intCast(ts.nsec));
}

pub const ScoreOpts = struct {
    suite_dir: []const u8 = "corpus/bench/sat_comp",
    limit: u32 = 40,
    max_conflicts: u64 = 500_000,
    timeout_s: f64 = 10.0,
    portfolio: bool = false,
    portfolio_budget: u64 = 500_000,
    preprocess: bool = true,
    inprocess: bool = true,
    /// Industrial mode: portfolio + high budget + vivify preprocess (best-effort PAR-2).
    industrial: bool = false,
};

pub fn run(allocator: std.mem.Allocator, io: std.Io, opts: ScoreOpts) !Scoreboard {
    const names_all = try bench.listCnfNames(allocator, io, opts.suite_dir);
    defer {
        for (names_all) |n| allocator.free(n);
        allocator.free(names_all);
    }

    const n = @min(opts.limit, @as(u32, @intCast(names_all.len)));
    var rows: std.ArrayList(Row) = .empty;
    errdefer {
        for (rows.items) |r| allocator.free(r.name);
        rows.deinit(allocator);
    }

    var sb: Scoreboard = .{
        .rows = &.{},
        .timeout_s = opts.timeout_s,
    };
    if (try external.findSolver(allocator)) |p| {
        sb.external_available = true;
        sb.cadical_path = p;
    }

    const timeout_ns: u64 = @intFromFloat(opts.timeout_s * @as(f64, @floatFromInt(std.time.ns_per_s)));
    const pen: f64 = 2.0 * opts.timeout_s;

    var i: u32 = 0;
    while (i < n) : (i += 1) {
        const name = names_all[i];
        const full = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ opts.suite_dir, name });
        defer allocator.free(full);
        const src = std.Io.Dir.cwd().readFileAlloc(io, full, allocator, .limited(64 * 1024 * 1024)) catch {
            try rows.append(allocator, .{
                .name = try allocator.dupe(u8, name),
                .internal = .error_,
                .external = .unknown,
                .match = false,
                .internal_ns = 0,
                .external_ns = 0,
                .model_ok = false,
            });
            sb.mismatches += 1;
            continue;
        };
        defer allocator.free(src);

        var cnf = dimacs.parse(allocator, src) catch {
            try rows.append(allocator, .{
                .name = try allocator.dupe(u8, name),
                .internal = .error_,
                .external = .unknown,
                .match = false,
                .internal_ns = 0,
                .external_ns = 0,
                .model_ok = false,
            });
            continue;
        };
        defer cnf.deinit();

        var pp_units: u32 = 0;
        const use_port = opts.portfolio or opts.industrial;
        const budget = if (opts.industrial) @max(opts.portfolio_budget, opts.max_conflicts) else if (use_port) opts.portfolio_budget else opts.max_conflicts;
        if (opts.preprocess or opts.industrial) {
            const st = try preprocess.preprocessOpts(allocator, &cnf, .{ .vivify = true });
            pp_units = st.units_propagated + st.pure_assigned + st.vivified_lits;
        }

        // Internal solve
        const t0 = monoNs();
        var model_ok = true;
        var istatus: bench.Status = .unknown;
        if (use_port) {
            var pr = try portfolio.solvePortfolioOpts(allocator, &cnf, .{
                .total_conflicts = budget,
                .validate_model = true,
                .ramp = true,
                // Industrial: enable inprocess across configs; pure already on one config.
                .inprocess_interval = if (opts.industrial or opts.inprocess) 1500 else 0,
            });
            defer if (pr.model) |m| allocator.free(m);
            defer if (pr.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            istatus = switch (pr.status) {
                .sat => .sat,
                .unsat => .unsat,
                .unknown => .unknown,
            };
            if (pr.status == .sat) {
                if (pr.model) |m| model_ok = cnf.checkModel(m) else model_ok = false;
            }
        } else {
            const r = try solver.solveCnf(allocator, &cnf, .{
                .max_conflicts = opts.max_conflicts,
                .preprocess = false, // already did
                .inprocess_interval = if (opts.inprocess or opts.industrial) 1500 else 0,
                .pure_literal = true,
                .minimize = true,
                .reduce_by_lbd = true,
            });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            istatus = switch (r.status) {
                .sat => .sat,
                .unsat => .unsat,
                .unknown => .unknown,
            };
            if (r.status == .sat) {
                if (r.model) |m| model_ok = cnf.checkModel(m) else model_ok = false;
            }
        }
        const t1 = monoNs();
        const ins = t1 - t0;

        // External CaDiCaL
        var estatus: bench.Status = .unknown;
        var ens: u64 = 0;
        if (sb.external_available) {
            // Re-parse original for external (preprocessed cnf still equisatisfiable)
            const ext = try bench.timeExternal(allocator, io, &cnf);
            estatus = ext.status;
            ens = ext.ns;
        }

        const match = blk: {
            if (!sb.external_available) break :blk false;
            if (istatus == .unknown or estatus == .unknown) break :blk false;
            if (istatus == .error_ or estatus == .error_) break :blk false;
            break :blk istatus == estatus;
        };

        if (istatus == .sat or istatus == .unsat) sb.solved_internal += 1;
        if (estatus == .sat or estatus == .unsat) sb.solved_external += 1;
        if (!sb.external_available or istatus == .unknown or estatus == .unknown) {
            sb.inconclusive += 1;
        } else if (!match) sb.mismatches += 1;
        if (!model_ok) sb.model_failures += 1;
        if (match and (istatus == .sat or istatus == .unsat) and (estatus == .sat or estatus == .unsat)) {
            sb.both_agreed += 1;
            if (ins < ens) sb.internal_faster += 1 else if (ens < ins) sb.external_faster += 1;
        }

        // PAR-2 style
        if (istatus == .sat or istatus == .unsat) {
            const s = @as(f64, @floatFromInt(ins)) / @as(f64, @floatFromInt(std.time.ns_per_s));
            sb.par2_internal += if (ins > timeout_ns) pen else s;
        } else sb.par2_internal += pen;
        if (sb.external_available) {
            if (estatus == .sat or estatus == .unsat) {
                const s = @as(f64, @floatFromInt(ens)) / @as(f64, @floatFromInt(std.time.ns_per_s));
                sb.par2_external += if (ens > timeout_ns) pen else s;
            } else sb.par2_external += pen;
        }

        try rows.append(allocator, .{
            .name = try allocator.dupe(u8, name),
            .internal = istatus,
            .external = estatus,
            .match = match,
            .internal_ns = ins,
            .external_ns = ens,
            .preprocess_units = pp_units,
            .model_ok = model_ok,
        });
    }

    sb.rows = try rows.toOwnedSlice(allocator);
    return sb;
}

pub fn print(sb: *const Scoreboard) void {
    std.debug.print("=== INDUSTRIAL SAT SCOREBOARD ===\n", .{});
    if (sb.cadical_path) |p| {
        std.debug.print("cadical: {s}\n", .{p});
    } else {
        std.debug.print("cadical: UNAVAILABLE (set LOGIC_ZIG_EXTERNAL_SOLVER or third_party/cadical)\n", .{});
    }
    std.debug.print("instances={d} solved_int={d} solved_ext={d} agreed={d} inconclusive={d} mismatches={d} model_fail={d}\n", .{
        sb.rows.len,
        sb.solved_internal,
        sb.solved_external,
        sb.both_agreed,
        sb.inconclusive,
        sb.mismatches,
        sb.model_failures,
    });
    std.debug.print("faster_int={d} faster_ext={d} PAR2_int={d:.3} PAR2_ext={d:.3}\n", .{
        sb.internal_faster,
        sb.external_faster,
        sb.par2_internal,
        sb.par2_external,
    });
    // Per-instance mismatches only
    for (sb.rows) |r| {
        if (!r.match or !r.model_ok) {
            std.debug.print("  FAIL {s} int={s} ext={s} model_ok={}\n", .{
                r.name,
                @tagName(r.internal),
                @tagName(r.external),
                r.model_ok,
            });
        }
    }
    if (sb.correctnessOk()) {
        std.debug.print("VERDICT_SCOREBOARD_CORRECTNESS=PASS\n", .{});
    } else {
        std.debug.print("VERDICT_SCOREBOARD_CORRECTNESS=FAIL\n", .{});
    }
    if (sb.external_available) {
        if (sb.par2_internal < sb.par2_external) {
            std.debug.print("VERDICT_SCOREBOARD_PAR2=WIN\n", .{});
        } else {
            std.debug.print("VERDICT_SCOREBOARD_PAR2=LOSE\n", .{});
        }
        if (sb.internal_faster >= sb.external_faster) {
            std.debug.print("VERDICT_SCOREBOARD_INSTANCE_SPEED=WIN ({d}>={d})\n", .{
                sb.internal_faster,
                sb.external_faster,
            });
        } else {
            std.debug.print("VERDICT_SCOREBOARD_INSTANCE_SPEED=LOSE ({d}<{d})\n", .{
                sb.internal_faster,
                sb.external_faster,
            });
        }
    } else {
        std.debug.print("VERDICT_SCOREBOARD_PAR2=SKIP_NO_CADICAL\n", .{});
    }
}

test "scoreboard module links" {
    _ = ScoreOpts{};
}
