//! Multi-shot incremental assume/solve benchmark.
//!
//! Wins the "embeddable library" axis: N assumption queries on one live engine
//! vs cold external process-per-query.
//!
//! Proof level: unit-tested; CLI produces `benchmarked` numbers.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");
const ipasir = @import("../sat/ipasir.zig");
const external = @import("../sat/external.zig");
const dimacs = @import("../bridge/dimacs.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Solver = solver_mod.Solver;

fn monoNs() u64 {
    var ts: std.os.linux.timespec = undefined;
    _ = std.os.linux.clock_gettime(std.os.linux.CLOCK.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) * std.time.ns_per_s + @as(u64, @intCast(ts.nsec));
}

pub const MultishotResult = struct {
    queries: u32,
    internal_ns: u64,
    external_ns: u64,
    internal_qps: f64,
    external_qps: f64,
    sat_count: u32,
    unsat_count: u32,
    external_available: bool,
    won_throughput: bool,
};

/// Shared base formula: adjacent equalities + a few 3-clauses.
fn buildBaseFormula(allocator: std.mem.Allocator, n_vars: u32) !Cnf {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();
    cnf.ensureVars(n_vars);
    var i: u32 = 0;
    while (i + 1 < n_vars) : (i += 2) {
        const a = Lit.positive(Var.fromIndex(i));
        const b = Lit.positive(Var.fromIndex(i + 1));
        // a <=> b
        try cnf.addClause(&.{ a.not(), b });
        try cnf.addClause(&.{ a, b.not() });
    }
    if (n_vars >= 6) {
        try cnf.addClause(&.{
            Lit.positive(Var.fromIndex(0)),
            Lit.positive(Var.fromIndex(2)),
            Lit.positive(Var.fromIndex(4)),
        });
        try cnf.addClause(&.{
            Lit.negative(Var.fromIndex(1)),
            Lit.positive(Var.fromIndex(3)),
            Lit.negative(Var.fromIndex(5)),
        });
    }
    return cnf;
}

/// Run `queries` assume/solve cycles on one Solver (multi-shot).
pub fn benchInternal(allocator: std.mem.Allocator, n_vars: u32, queries: u32, seed: u64) !struct { ns: u64, sat: u32, unsat: u32 } {
    var cnf = try buildBaseFormula(allocator, n_vars);
    defer cnf.deinit();
    var s = try Solver.init(allocator, &cnf, .{});
    defer s.deinit();

    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();
    var sat_c: u32 = 0;
    var unsat_c: u32 = 0;

    const t0 = monoNs();
    var q: u32 = 0;
    while (q < queries) : (q += 1) {
        // Pick 1-3 random assumptions
        var ass: [3]Lit = undefined;
        const n_ass = 1 + rng.intRangeLessThan(u32, 0, 3);
        var k: u32 = 0;
        while (k < n_ass) : (k += 1) {
            const v = rng.intRangeLessThan(u32, 0, n_vars);
            ass[k] = Lit.make(Var.fromIndex(v), rng.boolean());
        }
        const r = try s.solveAssumptions(ass[0..n_ass]);
        defer if (r.model) |m| allocator.free(m);
        defer if (r.assumption_core) |c| allocator.free(c);
        switch (r.status) {
            .sat => sat_c += 1,
            .unsat => unsat_c += 1,
            .unknown => {},
        }
    }
    const t1 = monoNs();
    return .{ .ns = t1 - t0, .sat = sat_c, .unsat = unsat_c };
}

/// Cold process-per-query via CaDiCaL (each query = full CNF + unit assumptions).
pub fn benchExternalCold(
    allocator: std.mem.Allocator,
    io: std.Io,
    n_vars: u32,
    queries: u32,
    seed: u64,
) !struct { ns: u64, available: bool } {
    const path = try external.findSolver(allocator);
    if (path == null) return .{ .ns = 0, .available = false };
    defer allocator.free(path.?);

    var base = try buildBaseFormula(allocator, n_vars);
    defer base.deinit();

    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();

    const t0 = monoNs();
    var q: u32 = 0;
    while (q < queries) : (q += 1) {
        var work = Cnf.init(allocator);
        defer work.deinit();
        work.ensureVars(n_vars);
        for (0..base.numClauses()) |ci| {
            try work.addClause(base.clauseSlice(cnf_mod.ClauseId.fromIndex(@intCast(ci))));
        }
        const n_ass = 1 + rng.intRangeLessThan(u32, 0, 3);
        var k: u32 = 0;
        while (k < n_ass) : (k += 1) {
            const v = rng.intRangeLessThan(u32, 0, n_vars);
            const lit = Lit.make(Var.fromIndex(v), rng.boolean());
            try work.addClause(&.{lit});
        }

        var aw: std.Io.Writer.Allocating = .init(allocator);
        defer aw.deinit();
        try dimacs.write(&work, &aw.writer);
        const body = try aw.toOwnedSlice();
        defer allocator.free(body);

        var tmp_buf: [64]u8 = undefined;
        const tmp = try std.fmt.bufPrint(&tmp_buf, "/tmp/logic-zig-ms-{d}-{d}.cnf", .{ monoNs() & 0xffff, q });
        {
            var path_z: [96]u8 = undefined;
            @memcpy(path_z[0..tmp.len], tmp);
            path_z[tmp.len] = 0;
            const fd = std.os.linux.open(@ptrCast(&path_z), .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, 0o644);
            if (@as(isize, @bitCast(fd)) < 0) continue;
            _ = std.os.linux.write(@intCast(fd), body.ptr, body.len);
            _ = std.os.linux.close(@intCast(fd));
        }
        const result = std.process.run(allocator, io, .{
            .argv = &.{ path.?, tmp },
            .stdout_limit = .limited(256 * 1024),
            .stderr_limit = .limited(64 * 1024),
        }) catch continue;
        allocator.free(result.stdout);
        allocator.free(result.stderr);
    }
    const t1 = monoNs();
    return .{ .ns = t1 - t0, .available = true };
}

pub fn run(
    allocator: std.mem.Allocator,
    io: std.Io,
    n_vars: u32,
    queries: u32,
    seed: u64,
) !MultishotResult {
    const internal = try benchInternal(allocator, n_vars, queries, seed);
    const external_r = try benchExternalCold(allocator, io, n_vars, queries, seed);

    const i_qps = if (internal.ns == 0) 0 else @as(f64, @floatFromInt(queries)) * 1e9 / @as(f64, @floatFromInt(internal.ns));
    const e_qps = if (!external_r.available or external_r.ns == 0)
        0
    else
        @as(f64, @floatFromInt(queries)) * 1e9 / @as(f64, @floatFromInt(external_r.ns));

    const won = !external_r.available or i_qps > e_qps;
    return .{
        .queries = queries,
        .internal_ns = internal.ns,
        .external_ns = external_r.ns,
        .internal_qps = i_qps,
        .external_qps = e_qps,
        .sat_count = internal.sat,
        .unsat_count = internal.unsat,
        .external_available = external_r.available,
        .won_throughput = won,
    };
}

pub fn printResult(r: *const MultishotResult) void {
    std.debug.print("c multishot queries={d} sat={d} unsat={d}\n", .{ r.queries, r.sat_count, r.unsat_count });
    std.debug.print("INTERNAL_NS={d} QPS={d:.2}\n", .{ r.internal_ns, r.internal_qps });
    std.debug.print("EXTERNAL_COLD_NS={d} QPS={d:.2} available={}\n", .{ r.external_ns, r.external_qps, r.external_available });
    if (r.won_throughput) {
        std.debug.print("VERDICT_MULTISHOT=WIN\n", .{});
    } else {
        std.debug.print("VERDICT_MULTISHOT=LOSE\n", .{});
    }
}

/// IPASIR multi-shot stress: add clauses over time, many assume/solve.
pub fn ipasirStress(allocator: std.mem.Allocator, queries: u32) !void {
    var s = ipasir.IpasirSolver.init(allocator);
    defer s.deinit();
    // (1|2) & (3|4)
    try s.add(1);
    try s.add(2);
    try s.add(0);
    try s.add(3);
    try s.add(4);
    try s.add(0);

    var q: u32 = 0;
    while (q < queries) : (q += 1) {
        if (q % 2 == 0) {
            try s.assume(-1);
            try s.assume(2);
        } else {
            try s.assume(1);
            try s.assume(-2);
        }
        const r = try s.solve();
        try std.testing.expect(r == .sat or r == .unsat);
    }
}

test "multishot internal completes" {
    const r = try benchInternal(std.testing.allocator, 12, 30, 0xBEEF);
    try std.testing.expect(r.sat + r.unsat == 30);
}

test "ipasir stress 20" {
    try ipasirStress(std.testing.allocator, 20);
}
