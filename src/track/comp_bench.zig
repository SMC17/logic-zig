//! Competition-slice PAR-2 + DRAT certificate bench on `corpus/bench/sat_comp`.
//!
//! Larger than the smoke suite: CaDiCaL unit tests + generated random 3-SAT.
//! Reports solved counts, PAR-2, mismatches, and external DRAT verified rate.

const std = @import("std");
const bench = @import("bench.zig");
const drat_external = @import("../sat/drat_external.zig");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");

pub const CompResult = struct {
    suite: bench.SuiteResult,
    drat_verified: u32 = 0,
    drat_failed: u32 = 0,
    drat_skipped: u32 = 0,
    drat_unavailable: bool = false,
    unique_faster: u32 = 0,
    unique_slower: u32 = 0,

    pub fn deinit(self: *CompResult, allocator: std.mem.Allocator) void {
        self.suite.deinit(allocator);
        self.* = undefined;
    }

    pub fn wonPar2(self: *const CompResult) bool {
        return self.suite.wonPar2();
    }

    pub fn correctnessOk(self: *const CompResult) bool {
        return self.suite.mismatches == 0 and self.suite.model_failures == 0 and self.drat_failed == 0;
    }
};

pub fn run(
    allocator: std.mem.Allocator,
    io: std.Io,
    suite_dir: []const u8,
    timeout_s: f64,
    max_conflicts: u64,
    check_drat: bool,
) !CompResult {
    var suite = try bench.runSuiteOpts(allocator, io, suite_dir, timeout_s, max_conflicts, false);
    errdefer suite.deinit(allocator);

    var unique_faster: u32 = 0;
    var unique_slower: u32 = 0;
    for (suite.instances) |ir| {
        if (!ir.match) continue;
        if (ir.internal_status != .sat and ir.internal_status != .unsat) continue;
        if (ir.external_status != .sat and ir.external_status != .unsat) continue;
        if (ir.internal_ns < ir.external_ns) unique_faster += 1 else if (ir.internal_ns > ir.external_ns) unique_slower += 1;
    }

    var drat_v: u32 = 0;
    var drat_f: u32 = 0;
    var drat_s: u32 = 0;
    var drat_unavail = false;

    if (check_drat) {
        const checker = try drat_external.findDratTrim(allocator);
        if (checker == null) {
            drat_unavail = true;
        } else {
            defer allocator.free(checker.?);
            // Cap external DRAT checks (re-solves with proof) for runtime.
            const max_drat: u32 = 40;
            var drat_budget: u32 = 0;
            for (suite.instances) |ir| {
                if (ir.internal_status != .unsat) {
                    drat_s += 1;
                    continue;
                }
                if (drat_budget >= max_drat) {
                    drat_s += 1;
                    continue;
                }
                drat_budget += 1;
                const full = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ suite_dir, ir.name });
                defer allocator.free(full);
                const src = std.Io.Dir.cwd().readFileAlloc(io, full, allocator, .limited(64 * 1024 * 1024)) catch {
                    drat_f += 1;
                    continue;
                };
                defer allocator.free(src);
                var cnf = dimacs.parse(allocator, src) catch {
                    drat_f += 1;
                    continue;
                };
                defer cnf.deinit();
                const r = try drat_external.solveAndCheckExternal(allocator, io, &cnf);
                switch (r.check) {
                    .verified => drat_v += 1,
                    .failed, .internal_error => drat_f += 1,
                    .unavailable => {
                        drat_unavail = true;
                        break;
                    },
                    .not_unsat => drat_s += 1,
                }
            }
        }
    }

    return .{
        .suite = suite,
        .drat_verified = drat_v,
        .drat_failed = drat_f,
        .drat_skipped = drat_s,
        .drat_unavailable = drat_unavail,
        .unique_faster = unique_faster,
        .unique_slower = unique_slower,
    };
}

pub fn printResult(r: *const CompResult) void {
    bench.printSuite(&r.suite);
    std.debug.print(
        "COMP_FASTER={d} COMP_SLOWER={d} DRAT_VERIFIED={d} DRAT_FAILED={d} DRAT_SKIP={d} DRAT_UNAVAIL={}\n",
        .{ r.unique_faster, r.unique_slower, r.drat_verified, r.drat_failed, r.drat_skipped, r.drat_unavailable },
    );
    if (r.correctnessOk()) {
        std.debug.print("VERDICT_COMP_CORRECTNESS=PASS\n", .{});
    } else {
        std.debug.print("VERDICT_COMP_CORRECTNESS=FAIL\n", .{});
    }
    if (r.suite.external_available) {
        if (r.wonPar2()) {
            std.debug.print("VERDICT_COMP_PAR2=WIN\n", .{});
        } else {
            std.debug.print("VERDICT_COMP_PAR2=LOSE\n", .{});
        }
        // Instance-level majority win
        if (r.unique_faster >= r.unique_slower) {
            std.debug.print("VERDICT_COMP_INSTANCE_SPEED=WIN ({d}>={d})\n", .{ r.unique_faster, r.unique_slower });
        } else {
            std.debug.print("VERDICT_COMP_INSTANCE_SPEED=LOSE ({d}<{d})\n", .{ r.unique_faster, r.unique_slower });
        }
    }
    if (!r.drat_unavailable and r.drat_failed == 0 and r.drat_verified > 0) {
        std.debug.print("VERDICT_DRAT_EXTERNAL=PASS\n", .{});
    } else if (r.drat_unavailable) {
        std.debug.print("VERDICT_DRAT_EXTERNAL=UNAVAILABLE\n", .{});
    } else if (r.drat_failed > 0) {
        std.debug.print("VERDICT_DRAT_EXTERNAL=FAIL\n", .{});
    } else {
        std.debug.print("VERDICT_DRAT_EXTERNAL=SKIP\n", .{});
    }
}

test "comp bench smoke on tiny suite path" {
    // Just ensure module links; full suite is CLI.
    _ = solver.SolveStatus.sat;
}
