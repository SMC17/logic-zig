//! HWMCC-style micro-bench: PDR/BMC on frozen AIGER demos + tiny synthetic nets.
//!
//! Reports wall time and status; compares safety engines for regressions.

const std = @import("std");
const aiger = @import("../bridge/aiger.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const kinduction = @import("../circuit/kinduction.zig");
const netlist_mod = @import("../circuit/netlist.zig");

const Netlist = netlist_mod.Netlist;

fn monoNs() u64 {
    var ts: std.os.linux.timespec = undefined;
    _ = std.os.linux.clock_gettime(std.os.linux.CLOCK.MONOTONIC, &ts);
    return @as(u64, @intCast(ts.sec)) * std.time.ns_per_s + @as(u64, @intCast(ts.nsec));
}

pub const CaseResult = struct {
    name: []const u8,
    engine: []const u8,
    status: []const u8,
    ns: u64,
    ok: bool,
};

pub const HwmccBenchResult = struct {
    cases: []CaseResult,
    all_ok: bool,
    total_ns: u64,

    pub fn deinit(self: *HwmccBenchResult, allocator: std.mem.Allocator) void {
        for (self.cases) |c| {
            allocator.free(c.name);
            allocator.free(c.engine);
            allocator.free(c.status);
        }
        allocator.free(self.cases);
        self.* = undefined;
    }
};

fn push(
    allocator: std.mem.Allocator,
    list: *std.ArrayList(CaseResult),
    name: []const u8,
    engine: []const u8,
    status: []const u8,
    ns: u64,
    ok: bool,
) !void {
    try list.append(allocator, .{
        .name = try allocator.dupe(u8, name),
        .engine = try allocator.dupe(u8, engine),
        .status = try allocator.dupe(u8, status),
        .ns = ns,
        .ok = ok,
    });
}

fn stuck0Net(allocator: std.mem.Allocator) !Netlist {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);
    return nl;
}

fn counterNet(allocator: std.mem.Allocator) !Netlist {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    const bad = try nl.allocNetNamed("bad");
    try nl.addGate(.not, &.{q0}, d0);
    try nl.addGate(.xor, &.{ q1, q0 }, d1);
    try nl.addGate(.and_, &.{ q1, q0 }, bad);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    try nl.addOutput(bad);
    return nl;
}

pub fn run(allocator: std.mem.Allocator, io: std.Io, frames: u32, aiger_dir: []const u8) !HwmccBenchResult {
    var cases: std.ArrayList(CaseResult) = .empty;
    errdefer {
        for (cases.items) |c| {
            allocator.free(c.name);
            allocator.free(c.engine);
            allocator.free(c.status);
        }
        cases.deinit(allocator);
    }
    var total: u64 = 0;
    var all_ok = true;

    // stuck0: should be proven safe
    {
        var nl = try stuck0Net(allocator);
        defer nl.deinit();
        const bad = nl.outputs.items[0];
        const t0 = monoNs();
        const r = try pdr.check(allocator, &nl, bad, frames);
        const ns = monoNs() - t0;
        defer if (r.cex_latches) |c| allocator.free(c);
        total += ns;
        const ok = r.status == .proven or r.status == .unknown;
        if (!ok) all_ok = false;
        try push(allocator, &cases, "stuck0", "pdr", @tagName(r.status), ns, ok);
    }
    {
        var nl = try stuck0Net(allocator);
        defer nl.deinit();
        const bad = nl.outputs.items[0];
        const t0 = monoNs();
        const r = try kinduction.search(allocator, &nl, bad, frames);
        const ns = monoNs() - t0;
        defer if (r.base.trace) |t| allocator.free(t);
        total += ns;
        const ok = r.status == .proven or r.status == .unknown;
        if (!ok) all_ok = false;
        try push(allocator, &cases, "stuck0", "kind", @tagName(r.status), ns, ok);
    }

    // counter: should be violated by frame 3
    {
        var nl = try counterNet(allocator);
        defer nl.deinit();
        const bad = nl.outputs.items[0];
        const t0 = monoNs();
        const r = try pdr.check(allocator, &nl, bad, frames);
        const ns = monoNs() - t0;
        defer if (r.cex_latches) |c| allocator.free(c);
        total += ns;
        const ok = r.status == .violated or r.status == .unknown;
        if (r.status == .proven) all_ok = false;
        try push(allocator, &cases, "counter", "pdr", @tagName(r.status), ns, ok and r.status != .proven);
    }
    {
        var nl = try counterNet(allocator);
        defer nl.deinit();
        const bad = nl.outputs.items[0];
        const t0 = monoNs();
        const r = try bmc.check(allocator, &nl, bad, @min(frames, 8));
        const ns = monoNs() - t0;
        defer if (r.trace) |t| allocator.free(t);
        total += ns;
        const ok = r.status == .violated;
        if (!ok) all_ok = false;
        try push(allocator, &cases, "counter", "bmc", @tagName(r.status), ns, ok);
    }

    // Optional AIGER files in dir
    if (std.Io.Dir.cwd().openDir(io, aiger_dir, .{ .iterate = true })) |dir_open| {
        var dir = dir_open;
        defer dir.close(io);
        var it = dir.iterate();
        while (try it.next(io)) |e| {
            if (e.kind != .file) continue;
            const is_aag = e.name.len >= 4 and std.mem.eql(u8, e.name[e.name.len - 4 ..], ".aag");
            const is_aig = e.name.len >= 4 and std.mem.eql(u8, e.name[e.name.len - 4 ..], ".aig");
            if (!is_aag and !is_aig) continue;
            const path = try std.fmt.allocPrint(allocator, "{s}/{s}", .{ aiger_dir, e.name });
            defer allocator.free(path);
            const src = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(4 * 1024 * 1024)) catch continue;
            defer allocator.free(src);
            var nl = aiger.parse(allocator, src) catch continue;
            defer nl.deinit();
            if (nl.outputs.items.len == 0 and nl.bad.items.len == 0) continue;
            const bad = if (nl.bad.items.len > 0) nl.bad.items[0] else nl.outputs.items[0];
            const t0 = monoNs();
            const r = try pdr.check(allocator, &nl, bad, frames);
            const ns = monoNs() - t0;
            defer if (r.cex_latches) |c| allocator.free(c);
            total += ns;
            // No oracle: any non-crash status is ok
            try push(allocator, &cases, e.name, "pdr", @tagName(r.status), ns, true);
        }
    } else |_| {}

    return .{
        .cases = try cases.toOwnedSlice(allocator),
        .all_ok = all_ok,
        .total_ns = total,
    };
}

pub fn printResult(r: *const HwmccBenchResult) void {
    for (r.cases) |c| {
        const ms = @as(f64, @floatFromInt(c.ns)) / 1e6;
        std.debug.print("c {s}/{s}: {s} {d:.3}ms ok={}\n", .{ c.name, c.engine, c.status, ms, c.ok });
    }
    std.debug.print("HWMCC_BENCH_TOTAL_MS={d:.3} cases={d}\n", .{
        @as(f64, @floatFromInt(r.total_ns)) / 1e6,
        r.cases.len,
    });
    if (r.all_ok) {
        std.debug.print("VERDICT_HWMCC=PASS\n", .{});
    } else {
        std.debug.print("VERDICT_HWMCC=FAIL\n", .{});
    }
}

test "hwmcc bench stuck0 kind" {
    // no io for dir miss
    const io = std.Options.debug_io;
    var r = try run(std.testing.allocator, io, 8, "corpus/bench/hwmcc");
    defer r.deinit(std.testing.allocator);
    try std.testing.expect(r.cases.len >= 4);
    try std.testing.expect(r.all_ok);
}
