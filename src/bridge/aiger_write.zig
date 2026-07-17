//! AIGER writer (ASCII + binary) from Netlist — HWMCC submission round-trips.
//!
//! Lowers OR/XOR/MUX to AND+NOT. Emits classic or extended headers.

const std = @import("std");
const Io = std.Io;
const netlist_mod = @import("../circuit/netlist.zig");
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;

pub const WriteError = error{
    Unsupported,
    TooComplex,
    WriteFailed,
} || std.mem.Allocator.Error;

pub const WriteOptions = struct {
    binary: bool = false,
    extended: bool = false,
    justice: []const NetId = &.{},
    outputs_as_bad: bool = true,
    symbols: bool = true,
};

const AndGate = struct { lhs: u32, rhs0: u32, rhs1: u32 };

const AndKey = struct {
    rhs0: u32,
    rhs1: u32,
    pub fn hash(self: AndKey) u64 {
        return (@as(u64, self.rhs0) << 32) ^ self.rhs1;
    }
    pub fn eql(a: AndKey, b: AndKey) bool {
        return a.rhs0 == b.rhs0 and a.rhs1 == b.rhs1;
    }
};

const AigBuilder = struct {
    allocator: std.mem.Allocator,
    next_var: u32 = 1,
    net_lit: std.AutoHashMapUnmanaged(u32, u32) = .{},
    /// Structural hash-cons of AND(rhs0,rhs1) → output lit (AIGER only has AND+NOT).
    and_hash: std.HashMapUnmanaged(AndKey, u32, struct {
        pub fn hash(_: @This(), k: AndKey) u64 {
            return k.hash();
        }
        pub fn eql(_: @This(), a: AndKey, b: AndKey) bool {
            return a.eql(b);
        }
    }, 80) = .{},
    ands: std.ArrayList(AndGate) = .empty,
    inputs: std.ArrayList(u32) = .empty,
    latches: std.ArrayList(struct { next: u32, init: u32 }) = .empty,
    outputs: std.ArrayList(u32) = .empty,
    bad: std.ArrayList(u32) = .empty,
    constraints: std.ArrayList(u32) = .empty,
    justice: std.ArrayList(u32) = .empty,
    fairness: std.ArrayList(u32) = .empty,
    input_nets: std.ArrayList(NetId) = .empty,
    latch_nets: std.ArrayList(NetId) = .empty,
    output_nets: std.ArrayList(NetId) = .empty,
    /// Count of hash hits (shared subexpressions — measures expansion savings).
    hash_hits: u32 = 0,

    fn deinit(self: *AigBuilder) void {
        self.net_lit.deinit(self.allocator);
        self.and_hash.deinit(self.allocator);
        self.ands.deinit(self.allocator);
        self.inputs.deinit(self.allocator);
        self.latches.deinit(self.allocator);
        self.outputs.deinit(self.allocator);
        self.bad.deinit(self.allocator);
        self.constraints.deinit(self.allocator);
        self.justice.deinit(self.allocator);
        self.fairness.deinit(self.allocator);
        self.input_nets.deinit(self.allocator);
        self.latch_nets.deinit(self.allocator);
        self.output_nets.deinit(self.allocator);
    }

    fn freshVar(self: *AigBuilder) u32 {
        const v = self.next_var;
        self.next_var += 1;
        return v;
    }

    fn litPos(_: *AigBuilder, v: u32) u32 {
        return 2 * v;
    }

    fn litNeg(_: *AigBuilder, lit: u32) u32 {
        return lit ^ 1;
    }

    /// Hash-consed AND with constant folding (AIGER canonical).
    fn mkAnd(self: *AigBuilder, a: u32, b: u32) !u32 {
        // Constant folding / absorption
        if (a == 0 or b == 0) return 0;
        if (a == 1) return b;
        if (b == 1) return a;
        if (a == b) return a;
        if (a == (b ^ 1)) return 0; // x ∧ ¬x

        var rhs0 = a;
        var rhs1 = b;
        if (rhs0 < rhs1) std.mem.swap(u32, &rhs0, &rhs1);
        const key = AndKey{ .rhs0 = rhs0, .rhs1 = rhs1 };
        if (self.and_hash.get(key)) |existing| {
            self.hash_hits += 1;
            return existing;
        }
        const v = self.freshVar();
        const lhs = self.litPos(v);
        try self.ands.append(self.allocator, .{ .lhs = lhs, .rhs0 = rhs0, .rhs1 = rhs1 });
        try self.and_hash.put(self.allocator, key, lhs);
        return lhs;
    }

    fn mkOr(self: *AigBuilder, a: u32, b: u32) !u32 {
        // De Morgan + hash-cons: a∨b = ¬(¬a ∧ ¬b)
        if (a == 1 or b == 1) return 1;
        if (a == 0) return b;
        if (b == 0) return a;
        if (a == b) return a;
        if (a == (b ^ 1)) return 1;
        const aand = try self.mkAnd(self.litNeg(a), self.litNeg(b));
        return self.litNeg(aand);
    }

    fn mkXor(self: *AigBuilder, a: u32, b: u32) !u32 {
        if (a == b) return 0;
        if (a == (b ^ 1)) return 1;
        if (a == 0) return b;
        if (b == 0) return a;
        if (a == 1) return self.litNeg(b);
        if (b == 1) return self.litNeg(a);
        // (a∨b) ∧ ¬(a∧b) with sharing
        const o = try self.mkOr(a, b);
        const an = try self.mkAnd(a, b);
        return try self.mkAnd(o, self.litNeg(an));
    }

    fn getOrCreateNet(self: *AigBuilder, n: NetId) !u32 {
        if (self.net_lit.get(n.index())) |l| return l;
        const v = self.freshVar();
        const lit = self.litPos(v);
        try self.net_lit.put(self.allocator, n.index(), lit);
        return lit;
    }

    fn setNet(self: *AigBuilder, n: NetId, lit: u32) !void {
        try self.net_lit.put(self.allocator, n.index(), lit);
    }
};

fn lowerNetlist(allocator: std.mem.Allocator, nl: *const Netlist, opts: WriteOptions) !AigBuilder {
    var b = AigBuilder{ .allocator = allocator };
    errdefer b.deinit();

    for (nl.inputs.items) |inp| {
        const v = b.freshVar();
        const lit = b.litPos(v);
        try b.setNet(inp, lit);
        try b.inputs.append(allocator, lit);
        try b.input_nets.append(allocator, inp);
    }

    for (nl.latches.items) |lat| {
        const v = b.freshVar();
        const lit = b.litPos(v);
        try b.setNet(lat.q, lit);
        try b.latch_nets.append(allocator, lat.q);
    }

    var pending = try allocator.alloc(bool, nl.gates.items.len);
    defer allocator.free(pending);
    @memset(pending, true);
    var progress = true;
    var guard: u32 = 0;
    while (progress and guard < nl.gates.items.len + 4) : (guard += 1) {
        progress = false;
        for (nl.gates.items, 0..) |g, gi| {
            if (!pending[gi]) continue;
            var ready = true;
            for (g.inputs) |inp| {
                if (b.net_lit.get(inp.index()) == null) {
                    var produced = false;
                    for (nl.gates.items) |og| {
                        if (og.output.index() == inp.index()) {
                            produced = true;
                            break;
                        }
                    }
                    if (produced) {
                        ready = false;
                        break;
                    }
                    _ = try b.getOrCreateNet(inp);
                }
            }
            if (!ready) continue;

            const out_lit: u32 = switch (g.kind) {
                .@"const" => if (g.const_val) @as(u32, 1) else 0,
                .buf => try b.getOrCreateNet(g.inputs[0]),
                .not => b.litNeg(try b.getOrCreateNet(g.inputs[0])),
                .and_, .and_n => blk: {
                    if (g.inputs.len == 0) break :blk @as(u32, 1);
                    var acc = try b.getOrCreateNet(g.inputs[0]);
                    var j: usize = 1;
                    while (j < g.inputs.len) : (j += 1) {
                        acc = try b.mkAnd(acc, try b.getOrCreateNet(g.inputs[j]));
                    }
                    break :blk acc;
                },
                .or_, .or_n => blk: {
                    if (g.inputs.len == 0) break :blk @as(u32, 0);
                    var acc = try b.getOrCreateNet(g.inputs[0]);
                    var j: usize = 1;
                    while (j < g.inputs.len) : (j += 1) {
                        acc = try b.mkOr(acc, try b.getOrCreateNet(g.inputs[j]));
                    }
                    break :blk acc;
                },
                .xor => try b.mkXor(try b.getOrCreateNet(g.inputs[0]), try b.getOrCreateNet(g.inputs[1])),
                .mux => blk: {
                    const s = try b.getOrCreateNet(g.inputs[0]);
                    const t = try b.getOrCreateNet(g.inputs[1]);
                    const f = try b.getOrCreateNet(g.inputs[2]);
                    const st = try b.mkAnd(s, t);
                    const nsf = try b.mkAnd(b.litNeg(s), f);
                    break :blk try b.mkOr(st, nsf);
                },
            };
            try b.setNet(g.output, out_lit);
            pending[gi] = false;
            progress = true;
        }
    }

    for (nl.latches.items) |lat| {
        const next = try b.getOrCreateNet(lat.d);
        const init: u32 = if (lat.init) |iv| (if (iv) @as(u32, 1) else 0) else 0;
        try b.latches.append(allocator, .{ .next = next, .init = init });
    }
    for (nl.outputs.items) |o| {
        try b.outputs.append(allocator, try b.getOrCreateNet(o));
        try b.output_nets.append(allocator, o);
    }
    // Bad: explicit list, or outputs if classic
    if (nl.bad.items.len > 0) {
        for (nl.bad.items) |bd| try b.bad.append(allocator, try b.getOrCreateNet(bd));
    } else if (opts.outputs_as_bad) {
        for (b.outputs.items) |ol| try b.bad.append(allocator, ol);
    }
    for (nl.constraints.items) |c| try b.constraints.append(allocator, try b.getOrCreateNet(c));
    const justice = if (opts.justice.len > 0) opts.justice else nl.justice.items;
    for (justice) |j| try b.justice.append(allocator, try b.getOrCreateNet(j));
    for (nl.fairness.items) |f| try b.fairness.append(allocator, try b.getOrCreateNet(f));
    return b;
}

fn encodeUnsigned(list: *std.ArrayList(u8), allocator: std.mem.Allocator, x: u32) !void {
    var v = x;
    while (v >= 0x80) {
        try list.append(allocator, @intCast((v & 0x7f) | 0x80));
        v >>= 7;
    }
    try list.append(allocator, @intCast(v));
}

pub fn write(allocator: std.mem.Allocator, nl: *const Netlist, opts: WriteOptions) WriteError![]u8 {
    var b = try lowerNetlist(allocator, nl, opts);
    defer b.deinit();

    const I: u32 = @intCast(b.inputs.items.len);
    const L: u32 = @intCast(b.latches.items.len);
    const O: u32 = @intCast(b.outputs.items.len);
    const A: u32 = @intCast(b.ands.items.len);
    const M = if (b.next_var > 1) b.next_var - 1 else 0;
    const Bd: u32 = @intCast(b.bad.items.len);
    const C: u32 = @intCast(b.constraints.items.len);
    const J: u32 = @intCast(b.justice.items.len);
    const F: u32 = @intCast(b.fairness.items.len);
    const use_ext = opts.extended or Bd > 0 or C > 0 or J > 0 or F > 0;

    if (opts.binary) {
        var out: std.ArrayList(u8) = .empty;
        errdefer out.deinit(allocator);
        const hdr = if (use_ext)
            try std.fmt.allocPrint(allocator, "aig {d} {d} {d} {d} {d} {d} {d} {d} {d}\n", .{ M, I, L, O, A, Bd, C, J, F })
        else
            try std.fmt.allocPrint(allocator, "aig {d} {d} {d} {d} {d}\n", .{ M, I, L, O, A });
        defer allocator.free(hdr);
        try out.appendSlice(allocator, hdr);
        for (b.latches.items) |lat| try encodeUnsigned(&out, allocator, lat.next);
        for (b.outputs.items) |ol| try encodeUnsigned(&out, allocator, ol);
        const ands_sorted = try allocator.dupe(AndGate, b.ands.items);
        defer allocator.free(ands_sorted);
        std.mem.sort(AndGate, ands_sorted, {}, struct {
            fn less(_: void, x: AndGate, y: AndGate) bool {
                return x.lhs < y.lhs;
            }
        }.less);
        for (ands_sorted) |ag| {
            var rhs0 = ag.rhs0;
            var rhs1 = ag.rhs1;
            if (rhs0 < rhs1) std.mem.swap(u32, &rhs0, &rhs1);
            if (ag.lhs < rhs0) return error.Unsupported;
            try encodeUnsigned(&out, allocator, ag.lhs - rhs0);
            try encodeUnsigned(&out, allocator, rhs0 - rhs1);
        }
        if (use_ext) {
            for (b.bad.items) |bl| try encodeUnsigned(&out, allocator, bl);
            for (b.constraints.items) |cl| try encodeUnsigned(&out, allocator, cl);
            for (b.justice.items) |jl| {
                try encodeUnsigned(&out, allocator, 1); // N=1 lit
                try encodeUnsigned(&out, allocator, jl);
            }
            for (b.fairness.items) |fl| try encodeUnsigned(&out, allocator, fl);
        }
        return try out.toOwnedSlice(allocator);
    }

    // ASCII via Allocating writer
    var aw: Io.Writer.Allocating = .init(allocator);
    defer aw.deinit();
    const w = &aw.writer;

    if (use_ext) {
        try w.print("aag {d} {d} {d} {d} {d} {d} {d} {d} {d}\n", .{ M, I, L, O, A, Bd, C, J, F });
    } else {
        try w.print("aag {d} {d} {d} {d} {d}\n", .{ M, I, L, O, A });
    }
    for (b.inputs.items) |il| try w.print("{d}\n", .{il});
    for (b.latches.items) |lat| try w.print("{d} {d}\n", .{ lat.next, lat.init });
    for (b.outputs.items) |ol| try w.print("{d}\n", .{ol});
    for (b.ands.items) |ag| {
        var rhs0 = ag.rhs0;
        var rhs1 = ag.rhs1;
        if (rhs0 < rhs1) std.mem.swap(u32, &rhs0, &rhs1);
        try w.print("{d} {d} {d}\n", .{ ag.lhs, rhs0, rhs1 });
    }
    if (use_ext) {
        for (b.bad.items) |bl| try w.print("{d}\n", .{bl});
        for (b.constraints.items) |cl| try w.print("{d}\n", .{cl});
        for (b.justice.items) |jl| try w.print("1 {d}\n", .{jl});
        for (b.fairness.items) |fl| try w.print("{d}\n", .{fl});
    }
    if (opts.symbols) {
        for (b.input_nets.items, 0..) |n, i| {
            if (n.index() < nl.names.items.len) {
                if (nl.names.items[n.index()]) |name| try w.print("i{d} {s}\n", .{ i, name });
            }
        }
        for (b.latch_nets.items, 0..) |n, i| {
            if (n.index() < nl.names.items.len) {
                if (nl.names.items[n.index()]) |name| try w.print("l{d} {s}\n", .{ i, name });
            }
        }
        for (b.output_nets.items, 0..) |n, i| {
            if (n.index() < nl.names.items.len) {
                if (nl.names.items[n.index()]) |name| try w.print("o{d} {s}\n", .{ i, name });
            }
        }
    }
    return try aw.toOwnedSlice();
}

pub fn writeAsciiSimple(allocator: std.mem.Allocator, nl: *const Netlist) ![]u8 {
    return write(allocator, nl, .{ .binary = false, .symbols = true });
}

pub fn writeBinary(allocator: std.mem.Allocator, nl: *const Netlist) ![]u8 {
    return write(allocator, nl, .{ .binary = true, .symbols = false });
}

test "aiger write read ascii roundtrip" {
    const aiger = @import("aiger.zig");
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.and_, &.{ a, b }, y);
    try nl.addOutput(y);

    const bytes = try writeAsciiSimple(std.testing.allocator, &nl);
    defer std.testing.allocator.free(bytes);

    var nl2 = try aiger.parse(std.testing.allocator, bytes);
    defer nl2.deinit();
    try std.testing.expect(nl2.inputs.items.len == 2);
    try std.testing.expect(nl2.outputs.items.len == 1);
    try std.testing.expect(nl2.gates.items.len >= 1);
}

test "aiger write binary read roundtrip" {
    const aiger = @import("aiger.zig");
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.and_, &.{ a, b }, y);
    try nl.addOutput(y);

    const bytes = try writeBinary(std.testing.allocator, &nl);
    defer std.testing.allocator.free(bytes);
    try std.testing.expect(std.mem.startsWith(u8, bytes, "aig "));

    var nl2 = try aiger.parse(std.testing.allocator, bytes);
    defer nl2.deinit();
    try std.testing.expect(nl2.inputs.items.len == 2);
    try std.testing.expect(nl2.outputs.items.len == 1);
}

test "aiger write latch roundtrip" {
    const aiger = @import("aiger.zig");
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);

    const bytes = try writeAsciiSimple(std.testing.allocator, &nl);
    defer std.testing.allocator.free(bytes);
    var nl2 = try aiger.parse(std.testing.allocator, bytes);
    defer nl2.deinit();
    try std.testing.expect(nl2.latches.items.len == 1);
}

test "aiger write hash-cons shares common AND" {
    // (a&b) used twice via OR structure should share the AND if lowered carefully
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const c = try nl.allocNetNamed("c");
    const ab = try nl.allocNetNamed("ab");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addInput(c);
    try nl.addGate(.and_, &.{ a, b }, ab);
    try nl.addGate(.or_, &.{ ab, c }, y); // expands to AND of negations but reuses ab
    try nl.addOutput(y);
    try nl.addOutput(ab); // same ab again

    var bld = try lowerNetlist(std.testing.allocator, &nl, .{});
    defer bld.deinit();
    // Structural hash should keep AND count modest
    try std.testing.expect(bld.ands.items.len >= 1);
    try std.testing.expect(bld.ands.items.len <= 4);
}

test "aiger write constant fold x and not x" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const na = try nl.allocNetNamed("na");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addGate(.not, &.{a}, na);
    try nl.addGate(.and_, &.{ a, na }, y);
    try nl.addOutput(y);
    const bytes = try writeAsciiSimple(std.testing.allocator, &nl);
    defer std.testing.allocator.free(bytes);
    // Output should be constant 0 → "0" as output lit
    try std.testing.expect(std.mem.indexOf(u8, bytes, "\n0\n") != null or std.mem.endsWith(u8, bytes, "\n0\n") or std.mem.indexOf(u8, bytes, " 0\n") != null);
}
