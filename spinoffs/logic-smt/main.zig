//! logic-smt — bit-vector bit-blast flagship.

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next();
    const cmd = iter.next() orelse {
        std.debug.print(
            \\logic-smt — BV bit-blast (profile=smt)
            \\  logic-smt demo-add
            \\  logic-smt profile
            \\
        , .{});
        return;
    };
    if (std.mem.eql(u8, cmd, "profile")) {
        const p = logic.profiles.get(.smt);
        std.debug.print("profile={s}\n{s}\n", .{ p.name, p.blurb });
        return;
    }
    if (std.mem.eql(u8, cmd, "demo-add")) {
        var w = logic.bv.BvWorld.init(gpa);
        defer w.deinit();
        const a = try w.mkConst(8, 40);
        const b = try w.mkConst(8, 2);
        const s = try w.mkAdd(a, b);
        const forty_two = try w.mkConst(8, 42);
        try w.assertEq(s, forty_two);
        const st = try w.checkSat();
        std.debug.print("40+2=42 => {s}\n", .{@tagName(st)});
        return;
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
