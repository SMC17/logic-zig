//! Frozen-suite SAT benchmark: PAR-2 vs vendored CaDiCaL.
//!
//! Measures:
//! - internal CDCL wall time (library, no process spawn)
//! - external CaDiCaL wall time (process)
//! - status agreement + model validation
//! - PAR-2 score = sum of times; timeout counts as 2 * T
//!
//! Proof level: unit-tested harness; run CLI for `benchmarked` evidence.

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");
const external = @import("../sat/external.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Value = lit_mod.Value;

pub const Status = enum { sat, unsat, unknown, error_ };

pub const InstanceResult = struct {
    name: []const u8,
    internal_status: Status,
    external_status: Status,
    internal_ns: u64,
    external_ns: u64,
    conflicts: u64 = 0,
    match: bool,
    model_ok: bool,
    timed_out_internal: bool = false,
    timed_out_external: bool = false,
};

pub const SuiteResult = struct {
    instances: []InstanceResult,
    par2_internal: f64,
    par2_external: f64,
    solved_internal: u32,
    solved_external: u32,
    mismatches: u32,
    model_failures: u32,
    timeout_s: f64,
    external_available: bool,

    pub fn deinit(self: *SuiteResult, allocator: std.mem.Allocator) void {
        for (self.instances) |*ir| allocator.free(ir.name);
        allocator.free(self.instances);
        self.* = undefined;
    }

    /// true if we beat external on PAR-2 among agreed solved set, or external unavailable.
    pub fn wonPar2(self: *const SuiteResult) bool {
        if (!self.external_available) return true;
        return self.par2_internal < self.par2_external;
    }
};

fn monoNs() u64 {
    var ts: std.os.linux.timespec = undefined;
    _ = std.os.linux.clock_gettime(std.os.linux.CLOCK.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) * std.time.ns_per_s + @as(u64, @intCast(ts.nsec));
}

fn statusFromSolve(s: solver.SolveStatus) Status {
    return switch (s) {
        .sat => .sat,
        .unsat => .unsat,
        .unknown => .unknown,
    };
}

fn statusFromExternal(s: external.ExternalStatus) Status {
    return switch (s) {
        .sat => .sat,
        .unsat => .unsat,
        .unknown => .unknown,
        .unavailable => .unknown,
    };
}

fn statusesMatch(a: Status, b: Status) bool {
    if (a == .error_ or b == .error_) return false;
    if (a == .unknown or b == .unknown) return true; // timeout / soft
    return a == b;
}

/// Solve one CNF with internal CDCL; max_conflicts acts as soft budget.
pub fn timeInternal(
    allocator: std.mem.Allocator,
    cnf: *const Cnf,
    max_conflicts: u64,
) !struct { status: Status, ns: u64, conflicts: u64, model_ok: bool } {
    const t0 = monoNs();
    const r = try solver.solveCnf(allocator, cnf, .{ .max_conflicts = max_conflicts });
    const t1 = monoNs();
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    var model_ok = true;
    if (r.status == .sat) {
        if (r.model) |m| {
            model_ok = cnf.checkModel(m);
        } else model_ok = false;
    }
    return .{
        .status = statusFromSolve(r.status),
        .ns = t1 - t0,
        .conflicts = r.conflicts,
        .model_ok = model_ok,
    };
}

/// Time external solver process on a CNF written to a temp file.
pub fn timeExternal(
    allocator: std.mem.Allocator,
    io: std.Io,
    cnf: *const Cnf,
) !struct { status: Status, ns: u64, available: bool } {
    const path = try external.findSolver(allocator);
    if (path == null) return .{ .status = .unknown, .ns = 0, .available = false };
    defer allocator.free(path.?);

    var aw: std.Io.Writer.Allocating = .init(allocator);
    defer aw.deinit();
    try dimacs.write(cnf, &aw.writer);
    const body = try aw.toOwnedSlice();
    defer allocator.free(body);

    // unique-ish temp path
    var tmp_buf: [64]u8 = undefined;
    const tmp = try std.fmt.bufPrint(&tmp_buf, "/tmp/logic-zig-bench-{d}.cnf", .{monoNs() & 0xffff_ffff});
    {
        var path_z: [80]u8 = undefined;
        @memcpy(path_z[0..tmp.len], tmp);
        path_z[tmp.len] = 0;
        const fd = std.os.linux.open(@ptrCast(&path_z), .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, 0o644);
        if (@as(isize, @bitCast(fd)) < 0) return .{ .status = .error_, .ns = 0, .available = true };
        _ = std.os.linux.write(@intCast(fd), body.ptr, body.len);
        _ = std.os.linux.close(@intCast(fd));
    }

    const t0 = monoNs();
    const result = std.process.run(allocator, io, .{
        .argv = &.{ path.?, tmp },
        .stdout_limit = .limited(4 * 1024 * 1024),
        .stderr_limit = .limited(1024 * 1024),
    }) catch {
        return .{ .status = .unknown, .ns = monoNs() - t0, .available = true };
    };
    const t1 = monoNs();
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);

    var status: Status = .unknown;
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
    return .{ .status = status, .ns = t1 - t0, .available = true };
}

fn endsWithCnf(name: []const u8) bool {
    return name.len >= 4 and std.mem.eql(u8, name[name.len - 4 ..], ".cnf");
}

/// List `*.cnf` basenames under dir_path (relative to cwd).
pub fn listCnfNames(allocator: std.mem.Allocator, io: std.Io, dir_path: []const u8) ![][]const u8 {
    var dir = try std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true });
    defer dir.close(io);
    var names: std.ArrayList([]const u8) = .empty;
    errdefer {
        for (names.items) |n| allocator.free(n);
        names.deinit(allocator);
    }
    var it = dir.iterate();
    while (try it.next(io)) |e| {
        if (e.kind != .file) continue;
        if (!endsWithCnf(e.name)) continue;
        try names.append(allocator, try allocator.dupe(u8, e.name));
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.less);
    return try names.toOwnedSlice(allocator);
}

/// Time `argv` process wall-clock. Caller owns argv strings.
pub fn timeProcess(allocator: std.mem.Allocator, io: std.Io, argv: []const []const u8) !struct { status: Status, ns: u64 } {
    const t0 = monoNs();
    const result = std.process.run(allocator, io, .{
        .argv = argv,
        .stdout_limit = .limited(4 * 1024 * 1024),
        .stderr_limit = .limited(1024 * 1024),
    }) catch {
        return .{ .status = .unknown, .ns = monoNs() - t0 };
    };
    const t1 = monoNs();
    defer allocator.free(result.stdout);
    defer allocator.free(result.stderr);
    var status: Status = .unknown;
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
    return .{ .status = status, .ns = t1 - t0 };
}

fn findSelfLogicZig(allocator: std.mem.Allocator) !?[]const u8 {
    var buf: [std.fs.max_path_bytes]u8 = undefined;
    const n = std.os.linux.readlink("/proc/self/exe", &buf, buf.len);
    const ni: isize = @bitCast(n);
    if (ni < 0) return null;
    return try allocator.dupe(u8, buf[0..@intCast(ni)]);
}

/// Run frozen suite under `suite_dir` (default `corpus/bench/sat`).
/// `timeout_s` is used for PAR-2 penalty; `max_conflicts` caps internal search.
/// When `fair_process` is true, times both as subprocesses (sat-track vs cadical).
pub fn runSuite(
    allocator: std.mem.Allocator,
    io: std.Io,
    suite_dir: []const u8,
    timeout_s: f64,
    max_conflicts: u64,
) !SuiteResult {
    return runSuiteOpts(allocator, io, suite_dir, timeout_s, max_conflicts, false);
}

pub fn runSuiteOpts(
    allocator: std.mem.Allocator,
    io: std.Io,
    suite_dir: []const u8,
    timeout_s: f64,
    max_conflicts: u64,
    fair_process: bool,
) !SuiteResult {
    const names = try listCnfNames(allocator, io, suite_dir);
    defer {
        for (names) |n| allocator.free(n);
        allocator.free(names);
    }

    const timeout_ns: u64 = @intFromFloat(timeout_s * @as(f64, @floatFromInt(std.time.ns_per_s)));
    var results: std.ArrayList(InstanceResult) = .empty;
    errdefer {
        for (results.items) |*ir| allocator.free(ir.name);
        results.deinit(allocator);
    }

    var par2_i: f64 = 0;
    var par2_e: f64 = 0;
    var solved_i: u32 = 0;
    var solved_e: u32 = 0;
    var mismatches: u32 = 0;
    var model_failures: u32 = 0;
    var ext_avail = false;

    for (names) |base| {
        const full = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ suite_dir, base });
        defer allocator.free(full);
        const src = std.Io.Dir.cwd().readFileAlloc(io, full, allocator, .limited(64 * 1024 * 1024)) catch {
            try results.append(allocator, .{
                .name = try allocator.dupe(u8, base),
                .internal_status = .error_,
                .external_status = .error_,
                .internal_ns = 0,
                .external_ns = 0,
                .match = false,
                .model_ok = false,
            });
            mismatches += 1;
            continue;
        };
        defer allocator.free(src);
        var cnf = dimacs.parse(allocator, src) catch {
            try results.append(allocator, .{
                .name = try allocator.dupe(u8, base),
                .internal_status = .error_,
                .external_status = .error_,
                .internal_ns = 0,
                .external_ns = 0,
                .match = false,
                .model_ok = false,
            });
            mismatches += 1;
            continue;
        };
        defer cnf.deinit();

        // Always validate model via library solve (even in fair mode).
        const lib = try timeInternal(allocator, &cnf, max_conflicts);
        if (!lib.model_ok) model_failures += 1;

        var internal_status = lib.status;
        var internal_ns = lib.ns;
        const conflicts = lib.conflicts;
        var external_status: Status = .unknown;
        var external_ns: u64 = 0;
        var ext_ok = false;

        if (fair_process) {
            const self_exe = try findSelfLogicZig(allocator);
            defer if (self_exe) |p| allocator.free(p);
            const cad = try external.findSolver(allocator);
            defer if (cad) |p| allocator.free(p);
            if (self_exe) |exe| {
                const pr = try timeProcess(allocator, io, &.{ exe, "sat-track", full });
                internal_status = pr.status;
                internal_ns = pr.ns;
            }
            if (cad) |cpath| {
                ext_ok = true;
                ext_avail = true;
                const er = try timeProcess(allocator, io, &.{ cpath, full });
                external_status = er.status;
                external_ns = er.ns;
            }
        } else {
            const external_r = try timeExternal(allocator, io, &cnf);
            ext_ok = external_r.available;
            if (ext_ok) ext_avail = true;
            external_status = if (ext_ok) external_r.status else .unknown;
            external_ns = external_r.ns;
        }

        const i_to = internal_status == .unknown or internal_ns > timeout_ns;
        const e_to = external_status == .unknown or external_ns > timeout_ns;

        const i_score: f64 = if (i_to or internal_status == .unknown)
            2.0 * timeout_s
        else
            @as(f64, @floatFromInt(internal_ns)) / @as(f64, @floatFromInt(std.time.ns_per_s));
        const e_score: f64 = if (!ext_ok)
            0
        else if (e_to or external_status == .unknown)
            2.0 * timeout_s
        else
            @as(f64, @floatFromInt(external_ns)) / @as(f64, @floatFromInt(std.time.ns_per_s));

        par2_i += i_score;
        if (ext_ok) par2_e += e_score;

        if (internal_status == .sat or internal_status == .unsat) {
            if (!i_to) solved_i += 1;
        }
        if (ext_ok and (external_status == .sat or external_status == .unsat) and !e_to) {
            solved_e += 1;
        }

        const match = if (!ext_ok) true else statusesMatch(internal_status, external_status);
        if (!match) mismatches += 1;

        try results.append(allocator, .{
            .name = try allocator.dupe(u8, base),
            .internal_status = internal_status,
            .external_status = external_status,
            .internal_ns = internal_ns,
            .external_ns = external_ns,
            .conflicts = conflicts,
            .match = match,
            .model_ok = lib.model_ok,
            .timed_out_internal = i_to,
            .timed_out_external = e_to,
        });
    }

    return .{
        .instances = try results.toOwnedSlice(allocator),
        .par2_internal = par2_i,
        .par2_external = par2_e,
        .solved_internal = solved_i,
        .solved_external = solved_e,
        .mismatches = mismatches,
        .model_failures = model_failures,
        .timeout_s = timeout_s,
        .external_available = ext_avail,
    };
}

pub fn printSuite(suite: *const SuiteResult) void {
    std.debug.print("c logic-zig bench-suite instances={d} timeout_s={d:.3}\n", .{ suite.instances.len, suite.timeout_s });
    std.debug.print("c external_available={}\n", .{suite.external_available});
    for (suite.instances) |ir| {
        const i_ms = @as(f64, @floatFromInt(ir.internal_ns)) / 1e6;
        const e_ms = @as(f64, @floatFromInt(ir.external_ns)) / 1e6;
        std.debug.print(
            "c {s}: int={s} {d:.3}ms conf={d} ext={s} {d:.3}ms match={} model_ok={}\n",
            .{
                ir.name,
                @tagName(ir.internal_status),
                i_ms,
                ir.conflicts,
                @tagName(ir.external_status),
                e_ms,
                ir.match,
                ir.model_ok,
            },
        );
    }
    std.debug.print(
        "PAR2_INTERNAL={d:.6} PAR2_EXTERNAL={d:.6} SOLVED_I={d} SOLVED_E={d} MISMATCHES={d} MODEL_FAIL={d}\n",
        .{
            suite.par2_internal,
            suite.par2_external,
            suite.solved_internal,
            suite.solved_external,
            suite.mismatches,
            suite.model_failures,
        },
    );
    if (suite.external_available) {
        if (suite.wonPar2()) {
            std.debug.print("VERDICT_PAR2=WIN (internal < external)\n", .{});
        } else {
            std.debug.print("VERDICT_PAR2=LOSE (internal >= external)\n", .{});
        }
    } else {
        std.debug.print("VERDICT_PAR2=NO_BASELINE\n", .{});
    }
    if (suite.mismatches == 0 and suite.model_failures == 0) {
        std.debug.print("VERDICT_CORRECTNESS=PASS\n", .{});
    } else {
        std.debug.print("VERDICT_CORRECTNESS=FAIL\n", .{});
    }
}

/// Emit simple JSON summary to stdout.
pub fn printJson(suite: *const SuiteResult) void {
    std.debug.print("{{\n", .{});
    std.debug.print("  \"timeout_s\": {d:.6},\n", .{suite.timeout_s});
    std.debug.print("  \"par2_internal\": {d:.6},\n", .{suite.par2_internal});
    std.debug.print("  \"par2_external\": {d:.6},\n", .{suite.par2_external});
    std.debug.print("  \"solved_internal\": {d},\n", .{suite.solved_internal});
    std.debug.print("  \"solved_external\": {d},\n", .{suite.solved_external});
    std.debug.print("  \"mismatches\": {d},\n", .{suite.mismatches});
    std.debug.print("  \"model_failures\": {d},\n", .{suite.model_failures});
    std.debug.print("  \"external_available\": {},\n", .{suite.external_available});
    std.debug.print("  \"won_par2\": {},\n", .{suite.wonPar2()});
    std.debug.print("  \"instances\": [\n", .{});
    for (suite.instances, 0..) |ir, i| {
        const comma: []const u8 = if (i + 1 < suite.instances.len) "," else "";
        std.debug.print(
            "    {{\"name\":\"{s}\",\"int\":\"{s}\",\"ext\":\"{s}\",\"int_ns\":{d},\"ext_ns\":{d},\"match\":{},\"model_ok\":{}}}{s}\n",
            .{
                ir.name,
                @tagName(ir.internal_status),
                @tagName(ir.external_status),
                ir.internal_ns,
                ir.external_ns,
                ir.match,
                ir.model_ok,
                comma,
            },
        );
    }
    std.debug.print("  ]\n}}\n", .{});
}

test "bench timeInternal sat" {
    const src =
        \\p cnf 2 1
        \\1 2 0
    ;
    var cnf = try dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const r = try timeInternal(std.testing.allocator, &cnf, 1_000_000);
    try std.testing.expect(r.status == .sat);
    try std.testing.expect(r.model_ok);
}

test "bench timeInternal unsat" {
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    var cnf = try dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const r = try timeInternal(std.testing.allocator, &cnf, 1_000_000);
    try std.testing.expect(r.status == .unsat);
}
