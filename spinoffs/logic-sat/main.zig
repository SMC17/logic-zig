//! logic-sat — portfolio / throughput-oriented SAT flagship.

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next();
    const cmd = iter.next() orelse {
        std.debug.print(
            \\logic-sat — portfolio CDCL (profile=sat-race)
            \\  logic-sat solve <file.cnf>
            \\  logic-sat portfolio <file.cnf>
            \\  logic-sat profile
            \\
        , .{});
        return;
    };
    const prof = logic.profiles.get(.sat_race);
    if (std.mem.eql(u8, cmd, "profile")) {
        std.debug.print("profile={s}\n{s}\n", .{ prof.name, prof.blurb });
        return;
    }
    if (std.mem.eql(u8, cmd, "solve") or std.mem.eql(u8, cmd, "portfolio")) {
        const path = iter.next() orelse {
            std.debug.print("missing cnf\n", .{});
            std.process.exit(2);
        };
        const src = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(64 * 1024 * 1024));
        defer gpa.free(src);
        var cnf = try logic.dimacs.parse(gpa, src);
        defer cnf.deinit();
        if (std.mem.eql(u8, cmd, "portfolio")) {
            const r = try logic.portfolio.solvePortfolio(gpa, &cnf, 2_000_000);
            defer if (r.model) |m| gpa.free(m);
            std.debug.print("s {s}\nc config={s} conflicts={d}\n", .{
                if (r.status == .sat) "SATISFIABLE" else if (r.status == .unsat) "UNSATISFIABLE" else "UNKNOWN",
                r.config_name,
                r.conflicts,
            });
            std.process.exit(if (r.status == .sat) 10 else if (r.status == .unsat) 20 else 0);
        }
        const r = try logic.solveCnf(gpa, &cnf, prof.solver);
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        std.debug.print("s {s}\nc conflicts={d}\n", .{
            if (r.status == .sat) "SATISFIABLE" else if (r.status == .unsat) "UNSATISFIABLE" else "UNKNOWN",
            r.conflicts,
        });
        std.process.exit(if (r.status == .sat) 10 else if (r.status == .unsat) 20 else 0);
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
