//! Differential testing against CaDiCaL with portable discovery.
//!
//! Search order (no hard-coded machine home required):
//! 1. env LOGIC_ZIG_EXTERNAL_SOLVER
//! 2. relative `third_party/cadical/build/cadical` from cwd
//! 3. relative `../third_party/cadical/build/cadical`
//! 4. path next to the running binary (platform executable directory + relative)

const std = @import("std");
const host = @import("../core/host.zig");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const dimacs_mod = @import("../bridge/dimacs.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const ExternalStatus = enum { sat, unsat, unknown, unavailable };

pub const DiffResult = struct {
    external: ExternalStatus,
    internal: solver_mod.SolveStatus,
    match: bool,
    solver_path: ?[]const u8 = null,
};

const pathExists = host.executableExists;

const readSelfExeDir = host.executableDir;

/// Caller frees returned path if non-null.
pub fn findSolver(allocator: std.mem.Allocator) !?[]const u8 {
    // 1) environment inherited at process startup
    if (readEnvSolver(allocator)) |p| return p;

    const rel = [_][]const u8{
        "third_party/cadical/build/cadical",
        "third_party/cadical/cadical",
        "../third_party/cadical/build/cadical",
        "cadical",
    };
    for (rel) |r| {
        if (pathExists(r)) return try allocator.dupe(u8, r);
    }

    // 4) next to binary: <exe_dir>/../third_party/... or <exe_dir>/third_party
    if (readSelfExeDir(allocator)) |dir| {
        defer allocator.free(dir);
        const candidates = [_][]const u8{
            "/../third_party/cadical/build/cadical",
            "/third_party/cadical/build/cadical",
            "/../../third_party/cadical/build/cadical",
        };
        for (candidates) |suf| {
            const full = try std.fmt.allocPrint(allocator, "{s}{s}", .{ dir, suf });
            if (pathExists(full)) return full;
            allocator.free(full);
        }
    }
    return null;
}

fn readEnvSolver(allocator: std.mem.Allocator) ?[]const u8 {
    return host.envPath(allocator, "LOGIC_ZIG_EXTERNAL_SOLVER");
}

fn solveExternalWithIo(allocator: std.mem.Allocator, io: std.Io, cnf: *const Cnf) !struct { status: ExternalStatus, path: ?[]const u8 } {
    const solver = try findSolver(allocator) orelse return .{ .status = .unavailable, .path = null };
    errdefer allocator.free(solver);

    // probe
    {
        const probe = std.process.run(allocator, io, .{
            .argv = &.{ solver, "--version" },
            .stdout_limit = .limited(256),
            .stderr_limit = .limited(256),
        }) catch {
            allocator.free(solver);
            return .{ .status = .unavailable, .path = null };
        };
        defer allocator.free(probe.stdout);
        defer allocator.free(probe.stderr);
    }

    var aw: std.Io.Writer.Allocating = .init(allocator);
    defer aw.deinit();
    try dimacs_mod.write(cnf, &aw.writer);
    const body = try aw.toOwnedSlice();
    defer allocator.free(body);

    var tmp_buf: [96]u8 = undefined;
    const tmp_path = try std.fmt.bufPrint(&tmp_buf, "/tmp/logic-zig-diff-{d}.cnf", .{host.monoNs()});
    try host.writeFile(io, tmp_path, body);
    defer std.Io.Dir.cwd().deleteFile(io, tmp_path) catch {};

    const result = std.process.run(allocator, io, .{
        .argv = &.{ solver, tmp_path },
        .stdout_limit = .limited(4 * 1024 * 1024),
        .stderr_limit = .limited(1024 * 1024),
    }) catch {
        allocator.free(solver);
        return .{ .status = .unknown, .path = null };
    };
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    var status: ExternalStatus = .unknown;
    if (std.mem.indexOf(u8, result.stdout, "UNSATISFIABLE") != null or
        std.mem.indexOf(u8, result.stderr, "UNSATISFIABLE") != null)
    {
        status = .unsat;
    } else if (std.mem.indexOf(u8, result.stdout, "SATISFIABLE") != null or
        std.mem.indexOf(u8, result.stderr, "SATISFIABLE") != null)
    {
        status = .sat;
    } else switch (result.term) {
        .exited => |code| {
            if (code == 10) status = .sat;
            if (code == 20) status = .unsat;
        },
        else => {},
    }
    return .{ .status = status, .path = solver };
}

pub fn differential(allocator: std.mem.Allocator, io: std.Io, cnf: *const Cnf) !DiffResult {
    const ext = try solveExternalWithIo(allocator, io, cnf);
    defer if (ext.path) |p| allocator.free(p);

    const r = try solver_mod.solveCnf(allocator, cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    if (ext.status == .unavailable) {
        return .{ .external = .unavailable, .internal = r.status, .match = true };
    }
    const match = switch (ext.status) {
        .sat => r.status == .sat,
        .unsat => r.status == .unsat,
        else => false,
    };
    return .{ .external = ext.status, .internal = r.status, .match = match };
}

pub fn fuzzExternal(
    allocator: std.mem.Allocator,
    io: std.Io,
    seed: u64,
    iters: u32,
    n_vars: u32,
) !struct { ran: u32, mismatches: u32, unavailable: bool, solver: ?[]const u8 } {
    const probe = try findSolver(allocator);
    if (probe == null) return .{ .ran = 0, .mismatches = 0, .unavailable = true, .solver = null };
    // keep probe for reporting; free by caller? we free after return path
    // Actually return owned solver path
    var mismatches: u32 = 0;
    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();
    var i: u32 = 0;
    while (i < iters) : (i += 1) {
        var cnf = Cnf.init(allocator);
        defer cnf.deinit();
        cnf.ensureVars(n_vars);
        var c: u32 = 0;
        while (c < n_vars * 4) : (c += 1) {
            var cl: [3]Lit = undefined;
            var k: u32 = 0;
            while (k < 3) : (k += 1) {
                cl[k] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n_vars)), rng.boolean());
            }
            try cnf.addClause(&cl);
        }
        const d = try differential(allocator, io, &cnf);
        if (d.external == .unavailable) {
            return .{ .ran = i, .mismatches = mismatches, .unavailable = true, .solver = probe };
        }
        if (!d.match) mismatches += 1;
    }
    return .{ .ran = iters, .mismatches = mismatches, .unavailable = false, .solver = probe };
}

test "findSolver relative" {
    // May or may not find cadical depending on cwd
    const p = try findSolver(std.testing.allocator);
    if (p) |path| {
        defer std.testing.allocator.free(path);
        try std.testing.expect(path.len > 0);
    }
}

test "external differential vs cadical if present" {
    const io = std.Options.debug_io;
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{a});
    try cnf.addClause(&.{a.not()});
    const d = try differential(std.testing.allocator, io, &cnf);
    if (d.external == .unavailable) return;
    try std.testing.expect(d.match);
    try std.testing.expect(d.external == .unsat);
}
