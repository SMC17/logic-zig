//! Minimal Yosys JSON netlist importer (combinational subset).
//!
//! Supports cell types: $and $or $xor $not $mux $logic_not $logic_and $logic_or
//! and gate-level $_AND_ $_OR_ $_XOR_ $_NOT_ $_MUX_
//! Connections use bit arrays of net integer IDs (Yosys "bits").

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const GateKind = netlist_mod.GateKind;

pub const YosysError = error{
    InvalidJson,
    Unsupported,
    MissingModule,
} || std.mem.Allocator.Error;

/// Parse a Yosys JSON document and build a Netlist for `module_name` (or first module).
pub fn parseModule(allocator: std.mem.Allocator, json_text: []const u8, module_name: ?[]const u8) YosysError!Netlist {
    var parsed = std.json.parseFromSlice(std.json.Value, allocator, json_text, .{}) catch return error.InvalidJson;
    defer parsed.deinit();
    const root = parsed.value;
    if (root != .object) return error.InvalidJson;
    const modules = root.object.get("modules") orelse return error.InvalidJson;
    if (modules != .object) return error.InvalidJson;

    var chosen: ?std.json.Value = null;
    var it = modules.object.iterator();
    while (it.next()) |entry| {
        if (module_name) |want| {
            if (std.mem.eql(u8, entry.key_ptr.*, want)) {
                chosen = entry.value_ptr.*;
                break;
            }
        } else {
            chosen = entry.value_ptr.*;
            break;
        }
    }
    const mod = chosen orelse return error.MissingModule;
    if (mod != .object) return error.InvalidJson;

    var nl = Netlist.init(allocator);
    errdefer nl.deinit();

    // Map Yosys bit id (i64) → NetId. Constants 0/1 are special.
    var bit_map: std.AutoHashMapUnmanaged(i64, NetId) = .{};
    defer bit_map.deinit(allocator);

    const getNet = struct {
        fn call(map: *std.AutoHashMapUnmanaged(i64, NetId), nlist: *Netlist, alloc: std.mem.Allocator, bit: i64) !NetId {
            if (map.get(bit)) |n| return n;
            // Yosys uses "0" and "1" as strings sometimes; numeric bits for nets.
            const n = try nlist.allocNet();
            try map.put(alloc, bit, n);
            return n;
        }
    }.call;

    // Ports
    if (mod.object.get("ports")) |ports| {
        if (ports == .object) {
            var pit = ports.object.iterator();
            while (pit.next()) |pe| {
                const port = pe.value_ptr.*;
                if (port != .object) continue;
                const dir = port.object.get("direction") orelse continue;
                const bits = port.object.get("bits") orelse continue;
                if (bits != .array) continue;
                const is_input = dir == .string and std.mem.eql(u8, dir.string, "input");
                const is_output = dir == .string and std.mem.eql(u8, dir.string, "output");
                for (bits.array.items) |b| {
                    const bit_id = jsonBitId(b) orelse continue;
                    if (bit_id == 0 or bit_id == 1) continue; // const driven
                    const net = try getNet(&bit_map, &nl, allocator, bit_id);
                    if (is_input) try nl.addInput(net);
                    if (is_output) try nl.addOutput(net);
                }
            }
        }
    }

    // Cells
    if (mod.object.get("cells")) |cells| {
        if (cells == .object) {
            var cit = cells.object.iterator();
            while (cit.next()) |ce| {
                const cell = ce.value_ptr.*;
                if (cell != .object) continue;
                const typ_v = cell.object.get("type") orelse continue;
                if (typ_v != .string) continue;
                const typ = typ_v.string;
                const conns = cell.object.get("connections") orelse continue;
                if (conns != .object) continue;

                try addCell(&nl, allocator, &bit_map, typ, conns);
            }
        }
    }

    // Drive constant bits if referenced — handled when connecting.

    return nl;
}

fn jsonBitId(v: std.json.Value) ?i64 {
    return switch (v) {
        .integer => |i| i,
        .string => |s| blk: {
            if (std.mem.eql(u8, s, "0")) break :blk 0;
            if (std.mem.eql(u8, s, "1")) break :blk 1;
            break :blk std.fmt.parseInt(i64, s, 10) catch null;
        },
        else => null,
    };
}

fn firstBit(conns: std.json.Value, port: []const u8) ?i64 {
    const arr = conns.object.get(port) orelse return null;
    if (arr != .array or arr.array.items.len == 0) return null;
    return jsonBitId(arr.array.items[0]);
}

fn addCell(
    nl: *Netlist,
    allocator: std.mem.Allocator,
    bit_map: *std.AutoHashMapUnmanaged(i64, NetId),
    typ: []const u8,
    conns: std.json.Value,
) !void {
    const getNet = struct {
        fn call(map: *std.AutoHashMapUnmanaged(i64, NetId), nlist: *Netlist, alloc: std.mem.Allocator, bit: i64) !NetId {
            if (bit == 0) {
                // Constant 0 net — create dedicated const gate once per call is wasteful but ok.
                const n = try nlist.allocNet();
                try nlist.addConst(n, false);
                return n;
            }
            if (bit == 1) {
                const n = try nlist.allocNet();
                try nlist.addConst(n, true);
                return n;
            }
            if (map.get(bit)) |n| return n;
            const n = try nlist.allocNet();
            try map.put(alloc, bit, n);
            return n;
        }
    }.call;

    // Sequential DFF / ADFF (ignore clock/reset for formal combo+latch model: D→Q latch)
    if (std.mem.eql(u8, typ, "$dff") or std.mem.eql(u8, typ, "$_DFF_P_") or
        std.mem.eql(u8, typ, "$_DFF_N_") or std.mem.eql(u8, typ, "$adff") or
        std.mem.eql(u8, typ, "$sdff") or std.mem.eql(u8, typ, "$_DFFE_PP_"))
    {
        const d_bit = firstBit(conns, "D") orelse return;
        const q_bit = firstBit(conns, "Q") orelse return;
        const d = try getNet(bit_map, nl, allocator, d_bit);
        const q = try getNet(bit_map, nl, allocator, q_bit);
        try nl.addLatch(d, q, false);
        return;
    }

    // NAND / NOR / XNOR as and/or/xor + not
    if (std.mem.eql(u8, typ, "$nand") or std.mem.eql(u8, typ, "$_NAND_")) {
        const a = try getNet(bit_map, nl, allocator, firstBit(conns, "A") orelse return);
        const b = try getNet(bit_map, nl, allocator, firstBit(conns, "B") orelse return);
        const y = try getNet(bit_map, nl, allocator, firstBit(conns, "Y") orelse return);
        const mid = try nl.allocNet();
        try nl.addGate(.and_, &.{ a, b }, mid);
        try nl.addGate(.not, &.{mid}, y);
        return;
    }
    if (std.mem.eql(u8, typ, "$nor") or std.mem.eql(u8, typ, "$_NOR_")) {
        const a = try getNet(bit_map, nl, allocator, firstBit(conns, "A") orelse return);
        const b = try getNet(bit_map, nl, allocator, firstBit(conns, "B") orelse return);
        const y = try getNet(bit_map, nl, allocator, firstBit(conns, "Y") orelse return);
        const mid = try nl.allocNet();
        try nl.addGate(.or_, &.{ a, b }, mid);
        try nl.addGate(.not, &.{mid}, y);
        return;
    }
    if (std.mem.eql(u8, typ, "$xnor") or std.mem.eql(u8, typ, "$_XNOR_")) {
        const a = try getNet(bit_map, nl, allocator, firstBit(conns, "A") orelse return);
        const b = try getNet(bit_map, nl, allocator, firstBit(conns, "B") orelse return);
        const y = try getNet(bit_map, nl, allocator, firstBit(conns, "Y") orelse return);
        const mid = try nl.allocNet();
        try nl.addGate(.xor, &.{ a, b }, mid);
        try nl.addGate(.not, &.{mid}, y);
        return;
    }

    const kind: ?GateKind = blk: {
        if (std.mem.eql(u8, typ, "$and") or std.mem.eql(u8, typ, "$_AND_") or std.mem.eql(u8, typ, "$logic_and"))
            break :blk .and_;
        if (std.mem.eql(u8, typ, "$or") or std.mem.eql(u8, typ, "$_OR_") or std.mem.eql(u8, typ, "$logic_or"))
            break :blk .or_;
        if (std.mem.eql(u8, typ, "$xor") or std.mem.eql(u8, typ, "$_XOR_"))
            break :blk .xor;
        if (std.mem.eql(u8, typ, "$xnor") or std.mem.eql(u8, typ, "$_XNOR_"))
            break :blk .xnor;
        if (std.mem.eql(u8, typ, "$nand") or std.mem.eql(u8, typ, "$_NAND_"))
            break :blk .nand;
        if (std.mem.eql(u8, typ, "$nor") or std.mem.eql(u8, typ, "$_NOR_"))
            break :blk .nor;
        if (std.mem.eql(u8, typ, "$not") or std.mem.eql(u8, typ, "$_NOT_") or std.mem.eql(u8, typ, "$logic_not") or std.mem.eql(u8, typ, "$_INV_"))
            break :blk .not;
        if (std.mem.eql(u8, typ, "$mux") or std.mem.eql(u8, typ, "$_MUX_") or std.mem.eql(u8, typ, "$pmux"))
            break :blk .mux;
        if (std.mem.eql(u8, typ, "$buf") or std.mem.eql(u8, typ, "$_BUF_") or std.mem.eql(u8, typ, "$pos"))
            break :blk .buf;
        break :blk null;
    };

    if (kind == null) return;

    const k = kind.?;
    switch (k) {
        .not, .buf => {
            const a_bit = firstBit(conns, "A") orelse return;
            const y_bit = firstBit(conns, "Y") orelse return;
            const a = try getNet(bit_map, nl, allocator, a_bit);
            const y = try getNet(bit_map, nl, allocator, y_bit);
            try nl.addGate(k, &.{a}, y);
        },
        .and_, .or_, .xor, .xnor, .nand, .nor => {
            const a_bit = firstBit(conns, "A") orelse return;
            const b_bit = firstBit(conns, "B") orelse return;
            const y_bit = firstBit(conns, "Y") orelse return;
            const a = try getNet(bit_map, nl, allocator, a_bit);
            const b = try getNet(bit_map, nl, allocator, b_bit);
            const y = try getNet(bit_map, nl, allocator, y_bit);
            try nl.addGate(k, &.{ a, b }, y);
        },
        .mux => {
            const s_bit = firstBit(conns, "S") orelse return;
            const a_bit = firstBit(conns, "A") orelse return;
            const b_bit = firstBit(conns, "B") orelse return;
            const y_bit = firstBit(conns, "Y") orelse return;
            const s = try getNet(bit_map, nl, allocator, s_bit);
            const a = try getNet(bit_map, nl, allocator, a_bit);
            const b = try getNet(bit_map, nl, allocator, b_bit);
            const y = try getNet(bit_map, nl, allocator, y_bit);
            try nl.addGate(.mux, &.{ s, b, a }, y);
        },
        else => {},
    }
}

test "yosys dff becomes latch" {
    const src =
        \\{
        \\  "modules": {
        \\    "top": {
        \\      "ports": {
        \\        "d": { "direction": "input", "bits": [2] },
        \\        "q": { "direction": "output", "bits": [3] }
        \\      },
        \\      "cells": {
        \\        "ff": {
        \\          "type": "$dff",
        \\          "connections": { "D": [2], "Q": [3], "CLK": [4] }
        \\        }
        \\      }
        \\    }
        \\  }
        \\}
    ;
    var nl = try parseModule(std.testing.allocator, src, "top");
    defer nl.deinit();
    try std.testing.expect(nl.latches.items.len == 1);
}

test "yosys json half-adder-ish" {
    const src =
        \\{
        \\  "modules": {
        \\    "top": {
        \\      "ports": {
        \\        "a": { "direction": "input", "bits": [2] },
        \\        "b": { "direction": "input", "bits": [3] },
        \\        "y": { "direction": "output", "bits": [4] }
        \\      },
        \\      "cells": {
        \\        "g1": {
        \\          "type": "$and",
        \\          "connections": {
        \\            "A": [2],
        \\            "B": [3],
        \\            "Y": [4]
        \\          }
        \\        }
        \\      }
        \\    }
        \\  }
        \\}
    ;
    var nl = try parseModule(std.testing.allocator, src, "top");
    defer nl.deinit();
    try std.testing.expect(nl.inputs.items.len == 2);
    try std.testing.expect(nl.outputs.items.len == 1);
    try std.testing.expect(nl.gates.items.len >= 1);
}
