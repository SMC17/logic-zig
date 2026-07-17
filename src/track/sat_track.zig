//! SAT competition track runner.
//!
//! Reads DIMACS CNF from a file (or stdin path), solves with logic-zig CDCL,
//! prints competition-style output:
//!   s SATISFIABLE / s UNSATISFIABLE / s UNKNOWN
//!   v <model lits> 0

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");

pub fn runFile(allocator: std.mem.Allocator, path: []const u8, io: std.Io) !u8 {
    const src = try std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(256 * 1024 * 1024));
    defer allocator.free(src);
    return runBytes(allocator, src);
}

pub fn runBytes(allocator: std.mem.Allocator, src: []const u8) !u8 {
    var cnf = try dimacs.parse(allocator, src);
    defer cnf.deinit();

    std.debug.print("c logic-zig sat-track\n", .{});
    std.debug.print("c vars={d} clauses={d}\n", .{ cnf.num_vars, cnf.numClauses() });

    const r = try solver.solveCnf(allocator, &cnf, .{ .max_conflicts = std.math.maxInt(u64) });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    switch (r.status) {
        .sat => {
            std.debug.print("s SATISFIABLE\n", .{});
            if (r.model) |m| {
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
            return 10;
        },
        .unsat => {
            std.debug.print("s UNSATISFIABLE\n", .{});
            return 20;
        },
        .unknown => {
            std.debug.print("s UNKNOWN\n", .{});
            return 0;
        },
    }
}

test "sat track unsat" {
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    var cnf = try dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const r = try solver.solveCnf(std.testing.allocator, &cnf, .{});
    try std.testing.expect(r.status == .unsat);
}
