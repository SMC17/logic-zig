//! logic-hwmcc — sequential safety / liveness flagship.

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
            \\logic-hwmcc — AIGER safety/liveness (profile=hwmcc)
            \\  logic-hwmcc track <file.aag|aig> [--frames N]
            \\  logic-hwmcc klive <file.aag> [--max-k K]
            \\  logic-hwmcc golden
            \\  logic-hwmcc profile
            \\
        , .{});
        return;
    };
    const prof = logic.profiles.get(.hwmcc);
    if (std.mem.eql(u8, cmd, "profile")) {
        std.debug.print("profile={s}\n{s}\nmax_frames={d}\n", .{ prof.name, prof.blurb, prof.max_frames });
        return;
    }
    if (std.mem.eql(u8, cmd, "golden")) {
        const r = try logic.golden.runAll(gpa, io);
        logic.golden.printResult(&r);
        if (r.failed != 0) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "track")) {
        var frames = prof.max_frames;
        var path: ?[]const u8 = null;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = try std.fmt.parseInt(u32, iter.next() orelse "16", 10);
            } else if (path == null) {
                path = a;
            }
        }
        const code = try logic.hwmcc_track.runFileOpts(gpa, path orelse {
            std.debug.print("missing aiger\n", .{});
            std.process.exit(2);
        }, io, .{ .max_frames = frames });
        std.process.exit(code);
    }
    if (std.mem.eql(u8, cmd, "klive")) {
        var max_k = prof.max_k_liveness;
        var path: ?[]const u8 = null;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--max-k")) {
                max_k = try std.fmt.parseInt(u32, iter.next() orelse "8", 10);
            } else if (path == null) {
                path = a;
            }
        }
        const src = try std.Io.Dir.cwd().readFileAlloc(io, path orelse {
            std.debug.print("missing aiger\n", .{});
            std.process.exit(2);
        }, gpa, .limited(16 * 1024 * 1024));
        defer gpa.free(src);
        var nl = try logic.aiger.parse(gpa, src);
        defer nl.deinit();
        const cert = try logic.certificate.kLiveCert(gpa, &nl, max_k, prof.max_frames);
        const text = try logic.certificate.writeKLiveCert(gpa, cert);
        defer gpa.free(text);
        std.debug.print("{s}", .{text});
        return;
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
