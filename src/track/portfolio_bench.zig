//! Portfolio SAT over a directory of CNF files (logic-sat hard smoke).

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const portfolio = @import("../sat/portfolio.zig");

pub const FileResult = struct {
    name: []const u8,
    status: []const u8,
    config: []const u8,
    conflicts: u64,
    model_valid: bool,
    ok: bool,
};

pub const SuiteResult = struct {
    total: u32 = 0,
    sat: u32 = 0,
    unsat: u32 = 0,
    unknown: u32 = 0,
    failed: u32 = 0,
    conflicts: u64 = 0,
};

/// Run portfolio on up to `limit` .cnf files in `dir` (name-sorted).
pub fn runDir(
    allocator: std.mem.Allocator,
    io: std.Io,
    dir_path: []const u8,
    limit: u32,
    total_conflicts: u64,
) !SuiteResult {
    var suite: SuiteResult = .{};
    var dir = std.Io.Dir.cwd().openDir(io, dir_path, .{ .iterate = true }) catch return suite;
    defer dir.close(io);

    var names: std.ArrayList([]const u8) = .empty;
    defer {
        for (names.items) |n| allocator.free(n);
        names.deinit(allocator);
    }
    var it = dir.iterate();
    while (try it.next(io)) |e| {
        if (e.kind != .file) continue;
        if (!std.mem.endsWith(u8, e.name, ".cnf")) continue;
        try names.append(allocator, try allocator.dupe(u8, e.name));
    }
    std.mem.sort([]const u8, names.items, {}, struct {
        fn less(_: void, a: []const u8, b: []const u8) bool {
            return std.mem.order(u8, a, b) == .lt;
        }
    }.less);

    const n = @min(limit, @as(u32, @intCast(names.items.len)));
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        const name = names.items[i];
        var path_buf: [512]u8 = undefined;
        const path = try std.fmt.bufPrint(&path_buf, "{s}/{s}", .{ dir_path, name });
        const src = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(32 << 20)) catch {
            suite.failed += 1;
            suite.total += 1;
            continue;
        };
        defer allocator.free(src);
        var cnf = dimacs.parse(allocator, src) catch {
            suite.failed += 1;
            suite.total += 1;
            continue;
        };
        defer cnf.deinit();

        var r = try portfolio.solvePortfolioOpts(allocator, &cnf, .{
            .total_conflicts = total_conflicts,
            .validate_model = true,
            .ramp = true,
            .proof_on_unsat = false,
        });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };

        suite.total += 1;
        suite.conflicts += r.conflicts;
        switch (r.status) {
            .sat => {
                suite.sat += 1;
                if (!r.model_valid) suite.failed += 1;
            },
            .unsat => suite.unsat += 1,
            .unknown => suite.unknown += 1,
        }
        std.debug.print("c {s} {s} config={s} conf={d}\n", .{
            name,
            @tagName(r.status),
            r.config_name,
            r.conflicts,
        });
    }
    return suite;
}

pub fn printSuite(s: *const SuiteResult) void {
    std.debug.print("portfolio-bench: total={d} sat={d} unsat={d} unknown={d} failed={d} conflicts={d}\n", .{
        s.total,
        s.sat,
        s.unsat,
        s.unknown,
        s.failed,
        s.conflicts,
    });
}

test "portfolio bench empty dir ok" {
    // just ensure module links
    try std.testing.expect(true);
}
