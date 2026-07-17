//! AIGER ASCII (`aag`) and binary (`aig`) reader → Netlist.
//!
//! Supports classic header `aag M I L O A` and extended
//! `aag M I L O A B C J F` (bad / constraint / justice / fairness).
//! Symbol table: i/l/o/a/b/j/f/c.

const std = @import("std");
const netlist_mod = @import("../circuit/netlist.zig");
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;

pub const AigerError = error{
    InvalidFormat,
    Unsupported,
    UnexpectedEof,
} || std.mem.Allocator.Error;

pub const Header = struct {
    bin: bool,
    M: u32,
    I: u32,
    L: u32,
    O: u32,
    A: u32,
    B: u32 = 0,
    C: u32 = 0,
    J: u32 = 0,
    F: u32 = 0,
};

pub fn parse(allocator: std.mem.Allocator, data: []const u8) AigerError!Netlist {
    if (data.len >= 4 and std.mem.startsWith(u8, data, "aig ")) {
        return parseBinary(allocator, data);
    }
    return parseAscii(allocator, data);
}

fn parseU(s: []const u8) !u32 {
    return std.fmt.parseInt(u32, s, 10) catch error.InvalidFormat;
}

fn decodeUnsigned(data: []const u8, pos: *usize) !u32 {
    var x: u32 = 0;
    var i: u32 = 0;
    while (true) {
        if (pos.* >= data.len) return error.UnexpectedEof;
        const ch = data[pos.*];
        pos.* += 1;
        x |= @as(u32, ch & 0x7f) << @intCast(7 * i);
        if ((ch & 0x80) == 0) return x;
        i += 1;
        if (i > 5) return error.InvalidFormat;
    }
}

pub fn encodeUnsigned(x: u32, out: *std.ArrayList(u8), allocator: std.mem.Allocator) !void {
    var v = x;
    while (v >= 0x80) {
        try out.append(allocator, @intCast((v & 0x7f) | 0x80));
        v >>= 7;
    }
    try out.append(allocator, @intCast(v));
}

fn parseHeaderLine(line: []const u8) !Header {
    var hit = std.mem.tokenizeAny(u8, std.mem.trim(u8, line, " \t\r"), " \t");
    const tag = hit.next() orelse return error.InvalidFormat;
    const bin = std.mem.eql(u8, tag, "aig");
    if (!bin and !std.mem.eql(u8, tag, "aag")) return error.InvalidFormat;
    var h: Header = .{
        .bin = bin,
        .M = try parseU(hit.next() orelse return error.InvalidFormat),
        .I = try parseU(hit.next() orelse return error.InvalidFormat),
        .L = try parseU(hit.next() orelse return error.InvalidFormat),
        .O = try parseU(hit.next() orelse return error.InvalidFormat),
        .A = try parseU(hit.next() orelse return error.InvalidFormat),
    };
    if (hit.next()) |bs| {
        h.B = try parseU(bs);
        if (hit.next()) |cs| {
            h.C = try parseU(cs);
            if (hit.next()) |js| {
                h.J = try parseU(js);
                if (hit.next()) |fs| h.F = try parseU(fs);
            }
        }
    }
    return h;
}

fn buildSkeleton(allocator: std.mem.Allocator, M: u32, I: u32) !struct { nl: Netlist, pos: []NetId, c0: NetId, c1: NetId } {
    var nl = Netlist.init(allocator);
    errdefer nl.deinit();
    const c0 = try nl.allocNetNamed("aig0");
    try nl.addConst(c0, false);
    const c1 = try nl.allocNetNamed("aig1");
    try nl.addConst(c1, true);

    var pos = try allocator.alloc(NetId, M + 1);
    errdefer allocator.free(pos);
    pos[0] = c0;
    var v: u32 = 1;
    while (v <= M) : (v += 1) {
        var name_buf: [32]u8 = undefined;
        const name = std.fmt.bufPrint(&name_buf, "v{d}", .{v}) catch return error.InvalidFormat;
        pos[v] = try nl.allocNetNamed(name);
    }
    v = 1;
    while (v <= I) : (v += 1) try nl.addInput(pos[v]);
    return .{ .nl = nl, .pos = pos, .c0 = c0, .c1 = c1 };
}

fn litToNet(nl: *Netlist, pos: []const NetId, c0: NetId, c1: NetId, lit: u32) !NetId {
    if (lit == 0) return c0;
    if (lit == 1) return c1;
    const v = lit / 2;
    const neg = lit % 2 == 1;
    if (v >= pos.len) return error.InvalidFormat;
    if (!neg) return pos[v];
    var name_buf: [40]u8 = undefined;
    const name = std.fmt.bufPrint(&name_buf, "n{d}", .{lit}) catch return error.InvalidFormat;
    const y = try nl.allocNetNamed(name);
    try nl.addGate(.not, &.{pos[v]}, y);
    return y;
}

fn parseAscii(allocator: std.mem.Allocator, data: []const u8) AigerError!Netlist {
    var lines = std.mem.splitScalar(u8, data, '\n');
    const header = lines.next() orelse return error.InvalidFormat;
    const h = try parseHeaderLine(header);
    if (h.bin) return error.InvalidFormat;
    if (h.M < h.I + h.L + h.A) return error.InvalidFormat;

    const sk = try buildSkeleton(allocator, h.M, h.I);
    defer allocator.free(sk.pos);
    var nl = sk.nl;
    errdefer nl.deinit();

    var i: u32 = 0;
    while (i < h.I) : (i += 1) _ = lines.next() orelse return error.InvalidFormat;

    i = 0;
    while (i < h.L) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        var it = std.mem.tokenizeAny(u8, std.mem.trim(u8, line, " \t\r"), " \t");
        const next_lit = try parseU(it.next() orelse return error.InvalidFormat);
        const qv = h.I + 1 + i;
        const d = try litToNet(&nl, sk.pos, sk.c0, sk.c1, next_lit);
        var init_val: ?bool = false;
        if (it.next()) |t| {
            const iv = try parseU(t);
            init_val = if (iv == 0) false else if (iv == 1) true else null;
        }
        try nl.addLatch(d, sk.pos[qv], init_val);
    }

    i = 0;
    while (i < h.O) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        const lit = try parseU(std.mem.trim(u8, line, " \t\r"));
        try nl.addOutput(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }

    i = 0;
    while (i < h.A) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        var it = std.mem.tokenizeAny(u8, std.mem.trim(u8, line, " \t\r"), " \t");
        const lhs = try parseU(it.next() orelse return error.InvalidFormat);
        const r0 = try parseU(it.next() orelse return error.InvalidFormat);
        const r1 = try parseU(it.next() orelse return error.InvalidFormat);
        if (lhs % 2 != 0) return error.InvalidFormat;
        const yv = lhs / 2;
        const a = try litToNet(&nl, sk.pos, sk.c0, sk.c1, r0);
        const b = try litToNet(&nl, sk.pos, sk.c0, sk.c1, r1);
        try nl.addGate(.and_, &.{ a, b }, sk.pos[yv]);
    }

    // Extended B/C sections (single lit per property)
    i = 0;
    while (i < h.B) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        const lit = try parseU(std.mem.trim(u8, line, " \t\r"));
        try nl.addBad(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }
    i = 0;
    while (i < h.C) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        const lit = try parseU(std.mem.trim(u8, line, " \t\r"));
        try nl.addConstraint(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }
    // Justice: N then N lits (may span lines). Fairness after J.
    i = 0;
    while (i < h.J) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        var it = std.mem.tokenizeAny(u8, std.mem.trim(u8, line, " \t\r"), " \t");
        const n = try parseU(it.next() orelse return error.InvalidFormat);
        var lits_left = n;
        var acc: ?NetId = null;
        while (lits_left > 0) {
            const tok = it.next() orelse blk: {
                const more = lines.next() orelse return error.InvalidFormat;
                it = std.mem.tokenizeAny(u8, std.mem.trim(u8, more, " \t\r"), " \t");
                break :blk it.next() orelse return error.InvalidFormat;
            };
            const lit = try parseU(tok);
            const net = try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit);
            if (acc) |a| {
                const y = try nl.allocNet();
                try nl.addGate(.or_, &.{ a, net }, y);
                acc = y;
            } else acc = net;
            lits_left -= 1;
        }
        if (acc) |a| try nl.addJustice(a);
    }
    i = 0;
    while (i < h.F) : (i += 1) {
        const line = lines.next() orelse return error.InvalidFormat;
        const lit = try parseU(std.mem.trim(u8, line, " \t\r"));
        try nl.addFairness(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }

    // Classic AIGER: outputs double as bad properties when B is absent.
    if (h.B == 0) {
        for (nl.outputs.items) |o| try nl.addBad(o);
    }

    try parseSymbols(allocator, &lines, &nl, h, sk.pos);
    return nl;
}

fn parseSymbols(
    allocator: std.mem.Allocator,
    lines: *std.mem.SplitIterator(u8, .scalar),
    nl: *Netlist,
    h: Header,
    pos: []const NetId,
) !void {
    while (lines.next()) |raw| {
        const line = std.mem.trim(u8, raw, " \t\r");
        if (line.len == 0) continue;
        if (line[0] == 'c') break;
        if (line.len < 2) continue;
        const kind = line[0];
        if (kind != 'i' and kind != 'l' and kind != 'o' and kind != 'a' and kind != 'b' and kind != 'j' and kind != 'f') continue;
        var rest = line[1..];
        var idx: u32 = 0;
        var j: usize = 0;
        while (j < rest.len and rest[j] >= '0' and rest[j] <= '9') : (j += 1) {
            idx = idx * 10 + (rest[j] - '0');
        }
        while (j < rest.len and (rest[j] == ' ' or rest[j] == '\t')) j += 1;
        const name = rest[j..];
        if (name.len == 0) continue;

        const net: ?NetId = switch (kind) {
            'i' => if (idx < h.I and idx + 1 < pos.len) pos[idx + 1] else null,
            'l' => if (idx < h.L and h.I + 1 + idx < pos.len) pos[h.I + 1 + idx] else null,
            'o' => if (idx < nl.outputs.items.len) nl.outputs.items[idx] else null,
            'b' => if (idx < nl.bad.items.len) nl.bad.items[idx] else if (idx < nl.outputs.items.len) nl.outputs.items[idx] else null,
            'j' => if (idx < nl.justice.items.len) nl.justice.items[idx] else null,
            'f' => if (idx < nl.fairness.items.len) nl.fairness.items[idx] else null,
            'a' => blk: {
                const v = h.I + h.L + 1 + idx;
                break :blk if (v < pos.len) pos[v] else null;
            },
            else => null,
        };
        if (net) |n| {
            const ni = n.index();
            if (ni < nl.names.items.len) {
                if (nl.names.items[ni]) |old| allocator.free(old);
                nl.names.items[ni] = try allocator.dupe(u8, name);
            }
        }
    }
}

fn parseBinary(allocator: std.mem.Allocator, data: []const u8) AigerError!Netlist {
    const nl_end = std.mem.indexOfScalar(u8, data, '\n') orelse return error.InvalidFormat;
    const h = try parseHeaderLine(data[0..nl_end]);
    if (!h.bin) return error.InvalidFormat;
    if (h.M < h.I + h.L + h.A) return error.InvalidFormat;

    const sk = try buildSkeleton(allocator, h.M, h.I);
    defer allocator.free(sk.pos);
    var nl = sk.nl;
    errdefer nl.deinit();

    var pos: usize = nl_end + 1;

    var i: u32 = 0;
    while (i < h.L) : (i += 1) {
        const next_lit = try decodeUnsigned(data, &pos);
        const qv = h.I + 1 + i;
        const d = try litToNet(&nl, sk.pos, sk.c0, sk.c1, next_lit);
        try nl.addLatch(d, sk.pos[qv], false);
    }
    i = 0;
    while (i < h.O) : (i += 1) {
        const lit = try decodeUnsigned(data, &pos);
        try nl.addOutput(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }
    i = 0;
    while (i < h.A) : (i += 1) {
        const lhs: u32 = 2 * (h.I + h.L + 1 + i);
        const delta0 = try decodeUnsigned(data, &pos);
        const delta1 = try decodeUnsigned(data, &pos);
        if (delta0 > lhs) return error.InvalidFormat;
        const rhs0 = lhs - delta0;
        if (delta1 > rhs0) return error.InvalidFormat;
        const rhs1 = rhs0 - delta1;
        const yv = lhs / 2;
        const a = try litToNet(&nl, sk.pos, sk.c0, sk.c1, rhs0);
        const b = try litToNet(&nl, sk.pos, sk.c0, sk.c1, rhs1);
        try nl.addGate(.and_, &.{ a, b }, sk.pos[yv]);
    }
    // Extended binary: B C J F as unsigned lits (justice simplified as single lit each)
    i = 0;
    while (i < h.B) : (i += 1) {
        const lit = try decodeUnsigned(data, &pos);
        try nl.addBad(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }
    i = 0;
    while (i < h.C) : (i += 1) {
        const lit = try decodeUnsigned(data, &pos);
        try nl.addConstraint(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }
    i = 0;
    while (i < h.J) : (i += 1) {
        const n = try decodeUnsigned(data, &pos);
        var k: u32 = 0;
        var acc: ?NetId = null;
        while (k < n) : (k += 1) {
            const lit = try decodeUnsigned(data, &pos);
            const net = try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit);
            if (acc) |a| {
                const y = try nl.allocNet();
                try nl.addGate(.or_, &.{ a, net }, y);
                acc = y;
            } else acc = net;
        }
        if (acc) |a| try nl.addJustice(a);
    }
    i = 0;
    while (i < h.F) : (i += 1) {
        const lit = try decodeUnsigned(data, &pos);
        try nl.addFairness(try litToNet(&nl, sk.pos, sk.c0, sk.c1, lit));
    }

    if (h.B == 0) {
        for (nl.outputs.items) |o| try nl.addBad(o);
    }
    if (pos < data.len) {
        var lines = std.mem.splitScalar(u8, data[pos..], '\n');
        try parseSymbols(allocator, &lines, &nl, h, sk.pos);
    }
    return nl;
}

test "aiger ascii and gate" {
    const src =
        \\aag 3 2 0 1 1
        \\2
        \\4
        \\6
        \\6 2 4
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.inputs.items.len == 2);
    try std.testing.expect(nl.outputs.items.len == 1);
    try std.testing.expect(nl.badProps().len == 1);
}

test "aiger ascii latch" {
    const src =
        \\aag 1 0 1 1 0
        \\2 0
        \\2
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.latches.items.len == 1);
}

test "aiger binary and gate" {
    var bytes: std.ArrayList(u8) = .empty;
    defer bytes.deinit(std.testing.allocator);
    try bytes.appendSlice(std.testing.allocator, "aig 3 2 0 1 1\n");
    try encodeUnsigned(6, &bytes, std.testing.allocator);
    try encodeUnsigned(2, &bytes, std.testing.allocator);
    try encodeUnsigned(2, &bytes, std.testing.allocator);
    var nl = try parse(std.testing.allocator, bytes.items);
    defer nl.deinit();
    try std.testing.expect(nl.inputs.items.len == 2);
    try std.testing.expect(nl.outputs.items.len == 1);
}

test "aiger extended bad" {
    // M I L O A B C J F — one bad different from output optional
    const src =
        \\aag 3 2 0 1 1 1 0 0 0
        \\2
        \\4
        \\6
        \\6 2 4
        \\6
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.bad.items.len == 1);
}

test "aiger symbol table renames" {
    const src =
        \\aag 3 2 0 1 1
        \\2
        \\4
        \\6
        \\6 2 4
        \\i0 clk
        \\i1 en
        \\o0 out
        \\c comment
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expectEqualStrings("clk", nl.names.items[nl.inputs.items[0].index()].?);
    try std.testing.expectEqualStrings("out", nl.names.items[nl.outputs.items[0].index()].?);
}

test "aiger justice multi-lit" {
    // M I L O A B C J F — one justice with two lits (OR)
    const src =
        \\aag 3 2 0 1 1 0 0 1 0
        \\2
        \\4
        \\6
        \\6 2 4
        \\2 2 4
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.justice.items.len == 1);
}

test "aiger constraint section" {
    const src =
        \\aag 3 2 0 1 1 0 1 0 0
        \\2
        \\4
        \\6
        \\6 2 4
        \\2
    ;
    var nl = try parse(std.testing.allocator, src);
    defer nl.deinit();
    try std.testing.expect(nl.constraints.items.len == 1);
}

test "aiger extended write read roundtrip" {
    const aiger_write = @import("aiger_write.zig");
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.and_, &.{ a, b }, y);
    try nl.addOutput(y);
    try nl.addBad(y);
    try nl.addJustice(a);
    const bytes = try aiger_write.write(std.testing.allocator, &nl, .{ .extended = true, .outputs_as_bad = false });
    defer std.testing.allocator.free(bytes);
    var nl2 = try parse(std.testing.allocator, bytes);
    defer nl2.deinit();
    try std.testing.expect(nl2.bad.items.len >= 1);
    try std.testing.expect(nl2.justice.items.len >= 1);
}
