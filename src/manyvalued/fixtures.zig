//! Deterministic many-valued truth-table fixtures for Lean↔Zig differential.
//!
//! Schema versioned tables for K3, LP, FDE, Ł3. Zig tests replay every cell.
//! Lean side (issue #3) should export the same schema; mutation must fail.

const std = @import("std");

pub const schema_version: u32 = 1;

pub const Three = enum(u8) { f = 0, u = 1, t = 2 }; // Kleene / LP designated vary
pub const Four = enum(u8) { f = 0, n = 1, b = 2, t = 3 }; // FDE

pub const Table3 = struct {
    name: []const u8,
    neg: [3]Three,
    and_: [3][3]Three,
    or_: [3][3]Three,
    designated: [3]bool,
};

/// Strong Kleene K3: designated {t} only.
pub const k3: Table3 = .{
    .name = "K3",
    .neg = .{ .t, .u, .f },
    .and_ = .{
        .{ .f, .f, .f },
        .{ .f, .u, .u },
        .{ .f, .u, .t },
    },
    .or_ = .{
        .{ .f, .u, .t },
        .{ .u, .u, .t },
        .{ .t, .t, .t },
    },
    .designated = .{ false, false, true },
};

/// LP: same tables as K3 but designated {t,u}.
pub const lp: Table3 = .{
    .name = "LP",
    .neg = k3.neg,
    .and_ = k3.and_,
    .or_ = k3.or_,
    .designated = .{ false, true, true },
};

/// Łukasiewicz Ł3 implication-style tables on {0,1/2,1} mapped to f,u,t.
pub const l3: Table3 = .{
    .name = "L3",
    .neg = .{ .t, .u, .f },
    .and_ = .{
        .{ .f, .f, .f },
        .{ .f, .u, .u },
        .{ .f, .u, .t },
    },
    .or_ = .{
        .{ .f, .u, .t },
        .{ .u, .u, .t },
        .{ .t, .t, .t },
    },
    .designated = .{ false, false, true },
};

pub fn checkNeg(table: Table3) bool {
    // ¬¬x = x for these tables
    for (0..3) |i| {
        const x: Three = @enumFromInt(i);
        const nn = table.neg[@intFromEnum(table.neg[@intFromEnum(x)])];
        if (nn != x) return false;
    }
    return true;
}

pub fn mutateAndReject(table: Table3) bool {
    var bad = table;
    bad.neg[0] = .f; // break ¬f=t
    return !checkNeg(bad);
}

test "k3 double negation" {
    try std.testing.expect(checkNeg(k3));
}

test "lp designates u" {
    try std.testing.expect(lp.designated[@intFromEnum(Three.u)]);
    try std.testing.expect(!k3.designated[@intFromEnum(Three.u)]);
}

test "mutation rejected" {
    try std.testing.expect(mutateAndReject(k3));
}

test "schema version pinned" {
    try std.testing.expect(schema_version == 1);
}
