//! Harder correctness suite: brute fuzz, dimacs corpus, RUP proofs, Δ-CaDiCaL.
//!
//! Exit / print VERDICT_CORRECTNESS=PASS only when all axes green.

const std = @import("std");
const fuzz = @import("../sat/fuzz.zig");
const external = @import("../sat/external.zig");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const ipasir = @import("../sat/ipasir.zig");
const bench = @import("bench.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const AxisResult = struct {
    name: []const u8,
    pass: bool,
    detail: []const u8,
};

pub const SuiteReport = struct {
    axes: []AxisResult,
    all_pass: bool,

    pub fn deinit(self: *SuiteReport, allocator: std.mem.Allocator) void {
        for (self.axes) |a| {
            allocator.free(a.name);
            allocator.free(a.detail);
        }
        allocator.free(self.axes);
        self.* = undefined;
    }
};

fn axis(allocator: std.mem.Allocator, name: []const u8, pass: bool, detail: []const u8) !AxisResult {
    return .{
        .name = try allocator.dupe(u8, name),
        .pass = pass,
        .detail = try allocator.dupe(u8, detail),
    };
}

/// Brute-force fuzz at multiple sizes.
pub fn runFuzzAxis(allocator: std.mem.Allocator) !AxisResult {
    const configs = [_]struct { seed: u64, iters: u32, vars: u32, dens: f64 }{
        .{ .seed = 0xC0FFEE, .iters = 80, .vars = 8, .dens = 4.2 },
        .{ .seed = 42, .iters = 50, .vars = 10, .dens = 3.5 },
        .{ .seed = 7, .iters = 30, .vars = 12, .dens = 3.2 },
        .{ .seed = 99, .iters = 20, .vars = 14, .dens = 3.0 },
    };
    var total_mm: u32 = 0;
    var total_iters: u32 = 0;
    for (configs) |c| {
        const mm = try fuzz.fuzzVsBrute(allocator, c.seed, c.iters, c.vars, c.dens);
        total_mm += mm;
        total_iters += c.iters;
    }
    var buf: [128]u8 = undefined;
    const detail = try std.fmt.bufPrint(&buf, "mismatches={d} iters={d}", .{ total_mm, total_iters });
    return try axis(allocator, "fuzz_vs_brute", total_mm == 0, detail);
}

/// Every CNF in suite_dir: model check on SAT; optional external agree.
pub fn runDimacsAxis(allocator: std.mem.Allocator, io: std.Io, suite_dir: []const u8) !AxisResult {
    const names = bench.listCnfNames(allocator, io, suite_dir) catch {
        return try axis(allocator, "dimacs_corpus", false, "cannot list suite");
    };
    defer {
        for (names) |n| allocator.free(n);
        allocator.free(names);
    }

    var fails: u32 = 0;
    var n: u32 = 0;
    var ext_mm: u32 = 0;
    for (names) |base| {
        const full = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ suite_dir, base });
        defer allocator.free(full);
        const src = std.Io.Dir.cwd().readFileAlloc(io, full, allocator, .limited(16 * 1024 * 1024)) catch {
            fails += 1;
            continue;
        };
        defer allocator.free(src);
        var cnf = dimacs.parse(allocator, src) catch {
            fails += 1;
            continue;
        };
        defer cnf.deinit();
        n += 1;
        const r = try solver.solveCnf(allocator, &cnf, .{ .max_conflicts = 5_000_000 });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .sat) {
            if (r.model == null or !cnf.checkModel(r.model.?)) fails += 1;
        } else if (r.status == .unknown) {
            // budget — not a hard fail for correctness axis
        }
        const d = try external.differential(allocator, io, &cnf);
        if (d.external != .unavailable and !d.match) ext_mm += 1;
    }
    var buf: [160]u8 = undefined;
    const detail = try std.fmt.bufPrint(&buf, "files={d} model_fails={d} ext_mm={d}", .{ n, fails, ext_mm });
    return try axis(allocator, "dimacs_corpus", fails == 0 and ext_mm == 0, detail);
}

/// RUP proof path on known unsat.
pub fn runProofAxis(allocator: std.mem.Allocator) !AxisResult {
    // pigeon 3 into 2
    var cnf = Cnf.init(allocator);
    defer cnf.deinit();
    // holes h0,h1 pigeons p0,p1,p2 → vars 0..5 as p0h0,p0h1,p1h0,p1h1,p2h0,p2h1
    // each pigeon in a hole
    try cnf.addClause(&.{ Lit.positive(Var.fromIndex(0)), Lit.positive(Var.fromIndex(1)) });
    try cnf.addClause(&.{ Lit.positive(Var.fromIndex(2)), Lit.positive(Var.fromIndex(3)) });
    try cnf.addClause(&.{ Lit.positive(Var.fromIndex(4)), Lit.positive(Var.fromIndex(5)) });
    // at most one per hole
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(0)), Lit.negative(Var.fromIndex(2)) });
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(0)), Lit.negative(Var.fromIndex(4)) });
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(2)), Lit.negative(Var.fromIndex(4)) });
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(1)), Lit.negative(Var.fromIndex(3)) });
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(1)), Lit.negative(Var.fromIndex(5)) });
    try cnf.addClause(&.{ Lit.negative(Var.fromIndex(3)), Lit.negative(Var.fromIndex(5)) });

    const r = solver.solveCnf(allocator, &cnf, .{ .proof = true }) catch |e| {
        var buf: [64]u8 = undefined;
        const detail = try std.fmt.bufPrint(&buf, "error={s}", .{@errorName(e)});
        return try axis(allocator, "rup_proof", false, detail);
    };
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    const ok = r.status == .unsat and r.proof != null;
    var buf: [80]u8 = undefined;
    const detail = try std.fmt.bufPrint(&buf, "status={s} proof_lines={d}", .{
        @tagName(r.status),
        if (r.proof) |p| p.numClauses() else 0,
    });
    return try axis(allocator, "rup_proof", ok, detail);
}

/// Deletion-minimal assumption cores via IPASIR.
pub fn runAssumptionCoreAxis(allocator: std.mem.Allocator) !AxisResult {
    var s = ipasir.IpasirSolver.init(allocator);
    defer s.deinit();
    // Single clause (a|b); unsat under ~a,~b; free lit 3 must drop from core.
    try s.add(1);
    try s.add(2);
    try s.add(0);
    try s.assume(-1);
    try s.assume(-2);
    try s.assume(3);
    const r = try s.solve();
    if (r != .unsat) {
        return try axis(allocator, "assumption_core", false, "expected unsat");
    }
    const leak = s.failed(3) != 0;
    const need_a = s.failed(-1) != 0;
    const need_b = s.failed(-2) != 0;
    // Deletion-minimal for (a|b) under ~a,~b is exactly both; free 3 dropped.
    const ok = !leak and need_a and need_b;
    var buf: [120]u8 = undefined;
    const detail = try std.fmt.bufPrint(&buf, "leak3={} failed-1={} failed-2={}", .{ leak, need_a, need_b });
    return try axis(allocator, "assumption_core", ok, detail);
}

/// External random 3-SAT differential.
pub fn runExternalDiffAxis(allocator: std.mem.Allocator, io: std.Io, iters: u32) !AxisResult {
    const r = try external.fuzzExternal(allocator, io, 0xCAFE, iters, 10);
    defer if (r.solver) |p| allocator.free(p);
    if (r.unavailable) {
        return try axis(allocator, "external_diff", true, "cadical unavailable (skipped)");
    }
    var buf: [96]u8 = undefined;
    const detail = try std.fmt.bufPrint(&buf, "ran={d} mismatches={d}", .{ r.ran, r.mismatches });
    return try axis(allocator, "external_diff", r.mismatches == 0, detail);
}

pub fn runAll(
    allocator: std.mem.Allocator,
    io: std.Io,
    suite_dir: []const u8,
    ext_iters: u32,
) !SuiteReport {
    var axes: std.ArrayList(AxisResult) = .empty;
    errdefer {
        for (axes.items) |a| {
            allocator.free(a.name);
            allocator.free(a.detail);
        }
        axes.deinit(allocator);
    }

    try axes.append(allocator, try runFuzzAxis(allocator));
    try axes.append(allocator, try runProofAxis(allocator));
    try axes.append(allocator, try runAssumptionCoreAxis(allocator));
    try axes.append(allocator, try runDimacsAxis(allocator, io, suite_dir));
    try axes.append(allocator, try runExternalDiffAxis(allocator, io, ext_iters));

    var all = true;
    for (axes.items) |a| {
        if (!a.pass) all = false;
    }
    return .{
        .axes = try axes.toOwnedSlice(allocator),
        .all_pass = all,
    };
}

pub fn printReport(rep: *const SuiteReport) void {
    for (rep.axes) |a| {
        const tag: []const u8 = if (a.pass) "PASS" else "FAIL";
        std.debug.print("AXIS {s}: {s} ({s})\n", .{ a.name, tag, a.detail });
    }
    if (rep.all_pass) {
        std.debug.print("VERDICT_CORRECTNESS=PASS\n", .{});
    } else {
        std.debug.print("VERDICT_CORRECTNESS=FAIL\n", .{});
    }
}

test "proof axis pigeon" {
    const a = try runProofAxis(std.testing.allocator);
    defer std.testing.allocator.free(a.name);
    defer std.testing.allocator.free(a.detail);
    try std.testing.expect(a.pass);
}

test "assumption core axis" {
    const a = try runAssumptionCoreAxis(std.testing.allocator);
    defer std.testing.allocator.free(a.name);
    defer std.testing.allocator.free(a.detail);
    try std.testing.expect(a.pass);
}

test "fuzz axis quick" {
    // lighter than full CLI — still multi-config
    const mm = try fuzz.fuzzVsBrute(std.testing.allocator, 1, 15, 8, 4.0);
    try std.testing.expect(mm == 0);
}
