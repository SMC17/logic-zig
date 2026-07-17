//! logic-ctl — bounded CTL flagship.

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next();
    const cmd = iter.next() orelse {
        std.debug.print(
            \\logic-ctl — bounded CTL (profile=ctl)
            \\  logic-ctl demo
            \\  logic-ctl profile
            \\
        , .{});
        return;
    };
    if (std.mem.eql(u8, cmd, "profile")) {
        const p = logic.profiles.get(.ctl);
        std.debug.print("profile={s}\n{s}\n", .{ p.name, p.blurb });
        return;
    }
    if (std.mem.eql(u8, cmd, "demo")) {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        const nq = try nl.allocNetNamed("nq");
        try nl.addConst(d, false);
        try nl.addGate(.not, &.{q}, nq);
        try nl.addLatch(d, q, false);
        const ag = try logic.ctl.checkAg(gpa, &nl, nq, 6);
        const ef = try logic.ctl.checkEf(gpa, &nl, q, 6);
        std.debug.print("AG(~q)={s} EF(q)={s}\n", .{ @tagName(ag.status), @tagName(ef.status) });
        return;
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
