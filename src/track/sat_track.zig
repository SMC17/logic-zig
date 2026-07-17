//! SAT competition track runner (SAT Race / SAT Competition style).
//!
//! Reads DIMACS CNF, solves with logic-zig CDCL (or portfolio), prints:
//!   c <comments: resources, config>
//!   s SATISFIABLE / s UNSATISFIABLE / s UNKNOWN
//!   v <model lits> 0
//!
//! Exit codes (competition convention):
//!   10 = SAT, 20 = UNSAT, 0 = UNKNOWN, 1 = error/parse

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");
const portfolio = @import("../sat/portfolio.zig");
const lit_mod = @import("../core/lit.zig");

pub const TrackOpts = struct {
    /// Soft conflict budget (UNKNOWN when hit).
    max_conflicts: u64 = std.math.maxInt(u64),
    /// Emit internal RUP proof log (verified before claiming UNSAT).
    proof: bool = false,
    /// Multi-config portfolio instead of single CDCL.
    portfolio: bool = false,
    /// Total portfolio conflict budget (split across configs).
    portfolio_budget: u64 = 2_000_000,
    /// Validate SAT models against original CNF before claiming sat.
    validate_model: bool = true,
    /// Print verbose resource comments.
    verbose: bool = true,
};

pub fn runFile(allocator: std.mem.Allocator, path: []const u8, io: std.Io) !u8 {
    return runFileOpts(allocator, path, io, .{});
}

pub fn runFileOpts(allocator: std.mem.Allocator, path: []const u8, io: std.Io, opts: TrackOpts) !u8 {
    const src = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(256 * 1024 * 1024)) catch |err| {
        std.debug.print("c error reading {s}: {s}\n", .{ path, @errorName(err) });
        std.debug.print("s UNKNOWN\n", .{});
        return 1;
    };
    defer allocator.free(src);
    return runBytesOpts(allocator, src, opts);
}

pub fn runBytes(allocator: std.mem.Allocator, src: []const u8) !u8 {
    return runBytesOpts(allocator, src, .{});
}

pub fn runBytesOpts(allocator: std.mem.Allocator, src: []const u8, opts: TrackOpts) !u8 {
    var cnf = dimacs.parse(allocator, src) catch |err| {
        std.debug.print("c parse error: {s}\n", .{@errorName(err)});
        std.debug.print("s UNKNOWN\n", .{});
        return 1;
    };
    defer cnf.deinit();

    if (opts.verbose) {
        std.debug.print("c logic-zig sat-track\n", .{});
        std.debug.print("c vars={d} clauses={d} max_conflicts={d} portfolio={} proof={}\n", .{
            cnf.num_vars,
            cnf.numClauses(),
            if (opts.portfolio) opts.portfolio_budget else opts.max_conflicts,
            opts.portfolio,
            opts.proof,
        });
    }

    if (opts.portfolio) {
        return runPortfolio(allocator, &cnf, opts);
    }
    return runSingle(allocator, &cnf, opts);
}

fn runSingle(allocator: std.mem.Allocator, cnf: *const @import("../sat/cnf.zig").Cnf, opts: TrackOpts) !u8 {
    const r = try solver.solveCnf(allocator, cnf, .{
        .max_conflicts = opts.max_conflicts,
        .proof = opts.proof,
        .complete_model = true,
    });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    if (opts.verbose) {
        std.debug.print("c conflicts={d} decisions={d} props={d} learned={d}\n", .{
            r.conflicts,
            r.decisions,
            r.propagations,
            r.learned,
        });
    }

    switch (r.status) {
        .sat => {
            if (opts.validate_model) {
                if (r.model) |m| {
                    if (!cnf.checkModel(m)) {
                        std.debug.print("c MODEL_INVALID — refusing SAT claim\n", .{});
                        std.debug.print("s UNKNOWN\n", .{});
                        return 0;
                    }
                    if (opts.verbose) std.debug.print("c model_valid=true\n", .{});
                }
            }
            std.debug.print("s SATISFIABLE\n", .{});
            if (r.model) |m| emitModel(m);
            return 10;
        },
        .unsat => {
            if (opts.proof) {
                if (r.proof) |*pf| {
                    const ok = try pf.verifyRup(allocator, cnf);
                    if (opts.verbose) std.debug.print("c rup_verified={}\n", .{ok});
                    if (!ok) {
                        std.debug.print("c RUP_FAILED — refusing UNSAT claim\n", .{});
                        std.debug.print("s UNKNOWN\n", .{});
                        return 0;
                    }
                }
            }
            std.debug.print("s UNSATISFIABLE\n", .{});
            return 20;
        },
        .unknown => {
            std.debug.print("s UNKNOWN\n", .{});
            return 0;
        },
    }
}

fn runPortfolio(allocator: std.mem.Allocator, cnf: *const @import("../sat/cnf.zig").Cnf, opts: TrackOpts) !u8 {
    var r = try portfolio.solvePortfolioOpts(allocator, cnf, .{
        .total_conflicts = opts.portfolio_budget,
        .proof_on_unsat = opts.proof,
        .validate_model = opts.validate_model,
        .ramp = true,
    });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    if (opts.verbose) {
        std.debug.print("c portfolio config={s} tried={d} conflicts={d} model_valid={}\n", .{
            r.config_name,
            r.configs_tried,
            r.conflicts,
            r.model_valid,
        });
    }

    switch (r.status) {
        .sat => {
            if (opts.validate_model and !r.model_valid) {
                std.debug.print("c MODEL_INVALID — refusing SAT claim\n", .{});
                std.debug.print("s UNKNOWN\n", .{});
                return 0;
            }
            std.debug.print("s SATISFIABLE\n", .{});
            if (r.model) |m| emitModel(m);
            return 10;
        },
        .unsat => {
            if (opts.proof) {
                if (r.proof) |*pf| {
                    const ok = try pf.verifyRup(allocator, cnf);
                    if (opts.verbose) std.debug.print("c rup_verified={}\n", .{ok});
                    if (!ok) {
                        std.debug.print("c RUP_FAILED — refusing UNSAT claim\n", .{});
                        std.debug.print("s UNKNOWN\n", .{});
                        return 0;
                    }
                }
            }
            std.debug.print("s UNSATISFIABLE\n", .{});
            return 20;
        },
        .unknown => {
            std.debug.print("s UNKNOWN\n", .{});
            return 0;
        },
    }
}

fn emitModel(m: []const lit_mod.Value) void {
    std.debug.print("v", .{});
    for (m, 0..) |v, i| {
        const d: i32 = @intCast(i + 1);
        if (v == .true_) {
            std.debug.print(" {d}", .{d});
        } else {
            std.debug.print(" -{d}", .{d});
        }
    }
    std.debug.print(" 0\n", .{});
}

test "sat track unsat" {
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    // Capture competition prints so parallel golden tests stay clean.
    const code = try runBytesOpts(std.testing.allocator, src, .{ .verbose = false });
    try std.testing.expect(code == 20);
}

test "sat track sat model" {
    const src =
        \\p cnf 2 1
        \\1 2 0
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{ .verbose = false, .validate_model = true });
    try std.testing.expect(code == 10);
}

test "sat track parse error" {
    const src = "not a cnf at all !!!";
    const code = try runBytesOpts(std.testing.allocator, src, .{ .verbose = false });
    try std.testing.expect(code == 1);
}

test "sat track budget unknown" {
    const src =
        \\p cnf 3 1
        \\1 2 3 0
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{
        .max_conflicts = 0,
        .verbose = false,
    });
    try std.testing.expect(code == 10 or code == 0);
}

test "sat track portfolio unsat" {
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{
        .portfolio = true,
        .portfolio_budget = 50_000,
        .proof = true,
        .verbose = false,
    });
    try std.testing.expect(code == 20);
}
