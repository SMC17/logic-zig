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
            \\  logic-hwmcc track <file.aag|aig> [--frames N] [--cert]
            \\  logic-hwmcc klive <file.aag> [--max-k K]
            \\  logic-hwmcc fair-demo
            \\  logic-hwmcc designs-demo
            \\  logic-hwmcc golden
            \\  logic-hwmcc stack
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
    if (std.mem.eql(u8, cmd, "fair-demo")) {
        // dual justice: one stuck, one toggle → proven_infinite
        {
            var nl = logic.Netlist.init(gpa);
            defer nl.deinit();
            const q0 = try nl.allocNetNamed("q0");
            const q1 = try nl.allocNetNamed("q1");
            const d0 = try nl.allocNetNamed("d0");
            const d1 = try nl.allocNetNamed("d1");
            try nl.addConst(d0, false);
            try nl.addGate(.not, &.{q1}, d1);
            try nl.addLatch(d0, q0, false);
            try nl.addLatch(d1, q1, false);
            const r = try logic.kliveness.check(gpa, &nl, &.{ q0, q1 }, 4, 16, 0);
            std.debug.print("fair dead+toggle: {s} k={d}\n", .{ @tagName(r.status), r.k });
        }
        // dual toggle lasso
        {
            var nl = logic.Netlist.init(gpa);
            defer nl.deinit();
            const q0 = try nl.allocNetNamed("q0");
            const q1 = try nl.allocNetNamed("q1");
            const d0 = try nl.allocNetNamed("d0");
            const d1 = try nl.allocNetNamed("d1");
            try nl.addGate(.not, &.{q0}, d0);
            try nl.addGate(.xor, &.{ q1, q0 }, d1);
            try nl.addLatch(d0, q0, false);
            try nl.addLatch(d1, q1, false);
            const r = try logic.kliveness.check(gpa, &nl, &.{ q0, q1 }, 1, 8, 8);
            std.debug.print("fair dual-toggle: {s}\n", .{@tagName(r.status)});
        }
        return;
    }
    if (std.mem.eql(u8, cmd, "stack")) {
        // Full stack smoke for this flagship
        const g = try logic.golden.runAll(gpa, io);
        logic.golden.printResult(&g);
        if (g.failed != 0) std.process.exit(1);
        // track stuck0 fixture
        const code = try logic.hwmcc_track.runFileOpts(gpa, "corpus/golden/aiger/stuck0.aag", io, .{ .max_frames = 12 });
        std.debug.print("c track stuck0 exit={d}\n", .{code});
        if (code == 1) std.process.exit(1); // unsafe would be wrong
        std.debug.print("STACK_OK\n", .{});
        return;
    }
    if (std.mem.eql(u8, cmd, "track")) {
        var frames = prof.max_frames;
        var path: ?[]const u8 = null;
        var cert = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = try std.fmt.parseInt(u32, iter.next() orelse "16", 10);
            } else if (std.mem.eql(u8, a, "--cert")) {
                cert = true;
            } else if (path == null) {
                path = a;
            }
        }
        const code = try logic.hwmcc_track.runFileOpts(gpa, path orelse {
            std.debug.print("missing aiger\n", .{});
            std.process.exit(2);
        }, io, .{ .max_frames = frames, .cert = cert });
        std.process.exit(code);
    }
    if (std.mem.eql(u8, cmd, "designs-demo")) {
        // 5-bit counter teeth
        {
            var d = try logic.designs.makeCounter(gpa, 5);
            defer d.nl.deinit();
            const r30 = try logic.bmc.check(gpa, &d.nl, d.bad, 30);
            defer if (r30.trace) |t| gpa.free(t);
            const r31 = try logic.bmc.check(gpa, &d.nl, d.bad, 31);
            defer if (r31.trace) |t| gpa.free(t);
            std.debug.print("counter5: bound30={s} bound31={s}\n", .{ @tagName(r30.status), @tagName(r31.status) });
        }
        // multi-stuck cert
        {
            var d = try logic.designs.makeMultiStuck0(gpa, 5);
            defer d.nl.deinit();
            const inv = try logic.certificate.fromPdrProven(gpa, &d.nl, d.bad, 24);
            if (inv) |*i| {
                defer {
                    var ii = i.*;
                    ii.deinit();
                }
                std.debug.print("multi-stuck5: cert verified={} clauses={d}\n", .{
                    try i.verify(gpa, &d.nl),
                    i.clauses.len,
                });
            }
        }
        // mutex
        {
            var d = try logic.designs.makeMutex(gpa, true);
            defer d.nl.deinit();
            const r = try logic.bmc.check(gpa, &d.nl, d.bad, 8);
            defer if (r.trace) |t| gpa.free(t);
            std.debug.print("mutex+constraint: {s}\n", .{@tagName(r.status)});
        }
        // one-hot ring
        {
            var d = try logic.designs.makeOneHotRing(gpa, 4);
            defer d.nl.deinit();
            var r = try logic.pdr.check(gpa, &d.nl, d.bad, 16);
            defer r.deinit(gpa);
            std.debug.print("onehot-ring4: {s}\n", .{@tagName(r.status)});
        }
        // johnson unsafe
        {
            var d = try logic.designs.makeJohnson(gpa, 3);
            defer d.nl.deinit();
            const r = try logic.bmc.check(gpa, &d.nl, d.bad, 12);
            defer if (r.trace) |t| gpa.free(t);
            std.debug.print("johnson3: {s}\n", .{@tagName(r.status)});
        }
        // dual-rail + parity
        {
            var d = try logic.designs.makeDualRailSafe(gpa);
            defer d.nl.deinit();
            var r = try logic.pdr.check(gpa, &d.nl, d.bad, 12);
            defer r.deinit(gpa);
            std.debug.print("dual-rail: {s}\n", .{@tagName(r.status)});
        }
        {
            var d = try logic.designs.makeParityNeverBad(gpa);
            defer d.nl.deinit();
            const r = try logic.kinduction.search(gpa, &d.nl, d.bad, 3);
            defer if (r.base.trace) |t| gpa.free(t);
            std.debug.print("parity-never: {s}\n", .{@tagName(r.status)});
        }
        return;
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
