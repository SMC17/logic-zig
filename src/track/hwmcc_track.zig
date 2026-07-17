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
const kinduction = @import("../circuit/kinduction.zig");
const justice = @import("../circuit/justice.zig");
const kliveness = @import("../circuit/kliveness.zig");
const certificate = @import("../cert/certificate.zig");
const netlist_mod = @import("../circuit/netlist.zig");

pub const HwmccOpts = struct {
    max_frames: u32 = 16,
    each: bool = false,
    justice: bool = false,
    lasso: bool = false,
    /// k-liveness infinite proof for justice (after lasso search).
    klive: bool = false,
    max_k: u32 = 8,
    /// On proven: re-check inductive cert and print text.
    cert: bool = false,
    /// Try k-induction between PDR and BMC (deeper competition path).
    kind: bool = true,
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

fn emitCert(allocator: std.mem.Allocator, nl: *netlist_mod.Netlist, bad: netlist_mod.NetId, max_frames: u32) !void {
    const inv = try certificate.fromPdrProven(allocator, nl, bad, max_frames);
    if (inv) |*i| {
        defer {
            var ii = i.*;
            ii.deinit();
        }
        const ok = try i.verify(allocator, nl);
        std.debug.print("c cert source={s} clauses={d} verified={}\n", .{
            @tagName(i.source),
            i.clauses.len,
            ok,
        });
        if (ok) {
            const text = try i.writeText(allocator);
            defer allocator.free(text);
            // prefix each line
            var lines = std.mem.splitScalar(u8, text, '\n');
            while (lines.next()) |ln| {
                if (ln.len == 0) continue;
                std.debug.print("c cert-line {s}\n", .{ln});
            }
        }
    } else {
        std.debug.print("c cert unavailable\n", .{});
    }
}

fn checkOne(allocator: std.mem.Allocator, nl: *netlist_mod.Netlist, bad: netlist_mod.NetId, max_frames: u32, do_cert: bool, use_kind: bool) !u8 {
    var pdr_r = try pdr.check(allocator, nl, bad, max_frames);
    defer pdr_r.deinit(allocator);
    switch (pdr_r.status) {
        .proven => {
            std.debug.print("c pdr proven frames={d} gens={d} ctg={d}\n", .{
                pdr_r.frames,
                pdr_r.generalizations,
                pdr_r.ctg_blocks,
            });
            if (do_cert) try emitCert(allocator, nl, bad, max_frames);
            return 0;
        },
        .violated => {
            std.debug.print("c pdr violated frames={d}\n", .{pdr_r.frames});
            return 1;
        },
        .unknown => {},
    }
    // k-induction: deep competition path before BMC bound-only answer
    if (use_kind) {
        const k_max = @min(max_frames, 8);
        const kr = try kinduction.search(allocator, nl, bad, k_max);
        defer if (kr.base.trace) |t| allocator.free(t);
        switch (kr.status) {
            .proven => {
                std.debug.print("c kind proven k={d}\n", .{kr.k});
                if (do_cert) try emitCert(allocator, nl, bad, max_frames);
                return 0;
            },
            .violated => {
                std.debug.print("c kind violated k={d}\n", .{kr.k});
                return 1;
            },
            .base_only, .unknown => {},
        }
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
            const code = try checkOne(allocator, &nl, bad, opts.max_frames, opts.cert, opts.kind);
            std.debug.print("{d}\n", .{code});
            if (code == 1) worst = 1;
            if (code == 2 and worst != 1) worst = 2;
        }
        return worst;
    }

    // Combined multi-property: PDR → k-induction (prop0) → BMC
    var pdr_r = try pdr.checkMulti(allocator, &nl, props, opts.max_frames);
    defer pdr_r.deinit(allocator);
    switch (pdr_r.status) {
        .proven => {
            std.debug.print("c pdr multi proven frames={d} gens={d} ctg={d}\n", .{
                pdr_r.frames,
                pdr_r.generalizations,
                pdr_r.ctg_blocks,
            });
            if (opts.cert and props.len > 0) try emitCert(allocator, &nl, props[0], opts.max_frames);
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

    if (opts.kind and props.len == 1) {
        const k_max = @min(opts.max_frames, 8);
        const kr = try kinduction.search(allocator, &nl, props[0], k_max);
        defer if (kr.base.trace) |t| allocator.free(t);
        switch (kr.status) {
            .proven => {
                std.debug.print("c kind proven k={d}\n", .{kr.k});
                if (opts.cert) try emitCert(allocator, &nl, props[0], opts.max_frames);
                std.debug.print("0\n", .{});
                return 0;
            },
            .violated => {
                std.debug.print("c kind violated k={d}\n", .{kr.k});
                std.debug.print("1\n", .{});
                return 1;
            },
            .base_only, .unknown => {},
        }
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

test "hwmcc empty bad treated as safe" {
    // O=0 B=0 → no properties
    const src =
        \\aag 1 0 1 0 0
        \\0 0
        \\c stuck latch, no outputs/bad
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{ .max_frames = 4 });
    try std.testing.expect(code == 0);
}

test "hwmcc multi bad one unsafe" {
    // two latches: stuck0 + init1 stuck1; B section both
    const src =
        \\aag 2 0 2 0 0 2 0 0 0
        \\0 0
        \\1 1
        \\2
        \\4
        \\c multi-bad: q0 safe, q1 unsafe
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{ .max_frames = 8 });
    try std.testing.expect(code == 1);
}

test "hwmcc constraint blocks bad" {
    // q' = !q, init 0, constraint ~q (lit 3), bad = q (B=2)
    // Header: M I L O A B C J F
    const src =
        \\aag 1 0 1 0 0 1 1 0 0
        \\3 0
        \\2
        \\3
        \\c toggle under constraint ~q — safe
    ;
    const code = try runBytesOpts(std.testing.allocator, src, .{ .max_frames = 8 });
    try std.testing.expect(code == 0 or code == 2);
}
