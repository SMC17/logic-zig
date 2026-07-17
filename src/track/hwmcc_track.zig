//! HWMCC-style safety track on AIGER (multi-property + extended props).
//!
//! - Parse AIGER (aag/aig) including extended B/C/J/F and symbol table
//! - Bad properties: `nl.badProps()` (explicit B section or classic outputs)
//! - Constraints C forced in BMC/PDR
//! - Optional justice/fairness path via `--justice`
//! - Run PDR then BMC fallback (or justice checker)
//! - Print: 0 = safe (proven), 1 = unsafe (CEX), 2 = unknown
//!   With multiple properties under --each: one result line per property

const std = @import("std");
const aiger = @import("../bridge/aiger.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const justice = @import("../circuit/justice.zig");
const kliveness = @import("../circuit/kliveness.zig");
const netlist_mod = @import("../circuit/netlist.zig");

pub const HwmccOpts = struct {
    max_frames: u32 = 16,
    each: bool = false,
    justice: bool = false,
    lasso: bool = false,
    /// k-liveness infinite proof for justice (after lasso search).
    klive: bool = false,
    max_k: u32 = 8,
};

pub fn runFile(allocator: std.mem.Allocator, path: []const u8, io: std.Io, max_frames: u32) !u8 {
    return runFileOpts(allocator, path, io, .{ .max_frames = max_frames });
}

pub fn runFileOpts(allocator: std.mem.Allocator, path: []const u8, io: std.Io, opts: HwmccOpts) !u8 {
    const src = try std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(64 * 1024 * 1024));
    defer allocator.free(src);
    return runBytesOpts(allocator, src, opts);
}

pub fn runBytes(allocator: std.mem.Allocator, src: []const u8, max_frames: u32) !u8 {
    return runBytesOpts(allocator, src, .{ .max_frames = max_frames });
}

// Backward-compat wrappers used by main/tests.
pub fn runFileOptsLegacy(allocator: std.mem.Allocator, path: []const u8, io: std.Io, max_frames: u32, each: bool) !u8 {
    return runFileOpts(allocator, path, io, .{ .max_frames = max_frames, .each = each });
}

pub fn runBytesOptsLegacy(allocator: std.mem.Allocator, src: []const u8, max_frames: u32, each: bool) !u8 {
    return runBytesOpts(allocator, src, .{ .max_frames = max_frames, .each = each });
}

fn checkOne(allocator: std.mem.Allocator, nl: *netlist_mod.Netlist, bad: netlist_mod.NetId, max_frames: u32) !u8 {
    const pdr_r = try pdr.check(allocator, nl, bad, max_frames);
    defer if (pdr_r.cex_latches) |c| allocator.free(c);
    switch (pdr_r.status) {
        .proven => {
            std.debug.print("c pdr proven frames={d} gens={d} ctg={d}\n", .{
                pdr_r.frames,
                pdr_r.generalizations,
                pdr_r.ctg_blocks,
            });
            return 0;
        },
        .violated => {
            std.debug.print("c pdr violated frames={d}\n", .{pdr_r.frames});
            return 1;
        },
        .unknown => {},
    }
    const b = try bmc.check(allocator, nl, bad, max_frames);
    defer if (b.trace) |t| allocator.free(t);
    return switch (b.status) {
        .violated => blk: {
            std.debug.print("c bmc violated bound={d}\n", .{b.bound});
            break :blk 1;
        },
        .safe_up_to_bound => blk: {
            std.debug.print("c bmc safe_up_to_bound k={d}\n", .{b.bound});
            break :blk 2;
        },
        .unknown => 2,
    };
}

pub fn runBytesOpts(allocator: std.mem.Allocator, src: []const u8, opts: HwmccOpts) !u8 {
    var nl = try aiger.parse(allocator, src);
    defer nl.deinit();

    const props = nl.badProps();
    std.debug.print("c hwmcc-track nets={d} latches={d} bad={d} constr={d} justice={d} fair={d} frames_max={d}\n", .{
        nl.num_nets,
        nl.latches.items.len,
        props.len,
        nl.constraints.items.len,
        nl.justice.items.len,
        nl.fairness.items.len,
        opts.max_frames,
    });

    if (opts.justice or (nl.justice.items.len > 0 and props.len == 0)) {
        return runJustice(allocator, &nl, opts);
    }

    if (props.len == 0) {
        std.debug.print("c no bad properties — treating as safe\n", .{});
        std.debug.print("0\n", .{});
        return 0;
    }

    if (opts.each) {
        var worst: u8 = 0;
        for (props, 0..) |bad, i| {
            const name = if (bad.index() < nl.names.items.len) nl.names.items[bad.index()] else null;
            std.debug.print("c property {d} {s}\n", .{ i, name orelse "?" });
            const code = try checkOne(allocator, &nl, bad, opts.max_frames);
            std.debug.print("{d}\n", .{code});
            if (code == 1) worst = 1;
            if (code == 2 and worst != 1) worst = 2;
        }
        return worst;
    }

    // Combined multi-property PDR then BMC
    const pdr_r = try pdr.checkMulti(allocator, &nl, props, opts.max_frames);
    defer if (pdr_r.cex_latches) |c| allocator.free(c);
    switch (pdr_r.status) {
        .proven => {
            std.debug.print("c pdr multi proven frames={d} gens={d} ctg={d}\n", .{
                pdr_r.frames,
                pdr_r.generalizations,
                pdr_r.ctg_blocks,
            });
            std.debug.print("0\n", .{});
            return 0;
        },
        .violated => {
            std.debug.print("c pdr multi violated frames={d}\n", .{pdr_r.frames});
            std.debug.print("1\n", .{});
            return 1;
        },
        .unknown => {},
    }

    const b = try bmc.checkMulti(allocator, &nl, props, opts.max_frames);
    defer if (b.trace) |t| allocator.free(t);
    switch (b.status) {
        .violated => {
            std.debug.print("c bmc multi violated bound={d}\n", .{b.bound});
            std.debug.print("1\n", .{});
            return 1;
        },
        .safe_up_to_bound => {
            std.debug.print("c bmc multi safe_up_to_bound k={d}\n", .{b.bound});
            std.debug.print("2\n", .{});
            return 2;
        },
        .unknown => {
            std.debug.print("2\n", .{});
            return 2;
        },
    }
}

fn runJustice(allocator: std.mem.Allocator, nl: *netlist_mod.Netlist, opts: HwmccOpts) !u8 {
    if (opts.klive or opts.lasso) {
        const kr = try kliveness.checkNetlist(allocator, nl, opts.max_k, opts.max_frames, if (opts.lasso or opts.klive) opts.max_frames else 0);
        switch (kr.status) {
            .proven_infinite => {
                std.debug.print("c klive proven_infinite k={d} conflicts={d}\n0\n", .{ kr.k, kr.conflicts });
                return 0;
            },
            .lasso_witness, .violated => {
                std.debug.print("c klive {s} k={d}\n1\n", .{ @tagName(kr.status), kr.k });
                return 1;
            },
            .unknown => {},
        }
    }

    const r = try justice.checkNetlist(allocator, nl, opts.max_frames, opts.lasso);
    defer if (r.trace) |t| allocator.free(t);
    switch (r.status) {
        .witness => {
            std.debug.print("c justice witness bound={d}", .{r.bound});
            if (r.stem) |s| std.debug.print(" stem={d}", .{s});
            if (r.loop_end) |e| std.debug.print(" loop_end={d}", .{e});
            std.debug.print("\n1\n", .{});
            return 1;
        },
        .no_witness_within_bound => {
            std.debug.print("c justice no_witness_within_bound k={d}\n2\n", .{r.bound});
            return 2;
        },
        .unknown => {
            std.debug.print("2\n", .{});
            return 2;
        },
    }
}

test "hwmcc track parse aiger" {
    const src =
        \\aag 3 2 0 1 1
        \\2
        \\4
        \\6
        \\6 2 4
    ;
    var nl = try aiger.parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.outputs.items.len == 1);
    try std.testing.expect(nl.badProps().len == 1);
}

test "hwmcc multi output or" {
    const src =
        \\aag 3 2 0 2 1
        \\2
        \\4
        \\6
        \\2
        \\6 2 4
    ;
    var nl = try aiger.parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.outputs.items.len == 2);
}

test "hwmcc extended bad props" {
    const src =
        \\aag 3 2 0 1 1 1 0 0 0
        \\2
        \\4
        \\6
        \\6 2 4
        \\6
    ;
    var nl = try aiger.parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.bad.items.len == 1);
    try std.testing.expect(nl.badProps().len == 1);
}
