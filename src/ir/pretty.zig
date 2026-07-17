//! Pretty-print ExprPool nodes.

const std = @import("std");
const Io = std.Io;
const expr_mod = @import("expr.zig");
const ExprPool = expr_mod.ExprPool;
const ExprId = expr_mod.ExprId;

pub fn write(pool: *const ExprPool, id: ExprId, writer: *Io.Writer) !void {
    try writePrec(pool, id, 0, writer);
}

fn writePrec(pool: *const ExprPool, id: ExprId, parent_prec: u8, writer: *Io.Writer) !void {
    const t = pool.tag(id);
    const prec: u8 = switch (t) {
        .false_, .true_, .var_, .not => 5,
        .and_ => 4,
        .xor => 3,
        .or_ => 2,
        .implies => 1,
        .iff => 0,
    };
    const need_paren = prec < parent_prec;
    if (need_paren) try writer.writeAll("(");
    switch (t) {
        .false_ => try writer.writeAll("false"),
        .true_ => try writer.writeAll("true"),
        .var_ => try writer.writeAll(pool.varName(pool.varOf(id))),
        .not => {
            try writer.writeAll("!");
            try writePrec(pool, pool.child(id), 5, writer);
        },
        .and_ => {
            try writePrec(pool, pool.left(id), 4, writer);
            try writer.writeAll(" & ");
            try writePrec(pool, pool.right(id), 4, writer);
        },
        .or_ => {
            try writePrec(pool, pool.left(id), 2, writer);
            try writer.writeAll(" | ");
            try writePrec(pool, pool.right(id), 2, writer);
        },
        .xor => {
            try writePrec(pool, pool.left(id), 3, writer);
            try writer.writeAll(" ^ ");
            try writePrec(pool, pool.right(id), 3, writer);
        },
        .implies => {
            try writePrec(pool, pool.left(id), 1, writer);
            try writer.writeAll(" -> ");
            try writePrec(pool, pool.right(id), 1, writer);
        },
        .iff => {
            try writePrec(pool, pool.left(id), 0, writer);
            try writer.writeAll(" <-> ");
            try writePrec(pool, pool.right(id), 0, writer);
        },
    }
    if (need_paren) try writer.writeAll(")");
}

pub fn toString(allocator: std.mem.Allocator, pool: *const ExprPool, id: ExprId) ![]u8 {
    var aw: Io.Writer.Allocating = .init(allocator);
    defer aw.deinit();
    try write(pool, id, &aw.writer);
    return try aw.toOwnedSlice();
}

test "pretty roundtrip shape" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkVarNamed("a");
    const b = try pool.mkVarNamed("b");
    const e = try pool.mkOr(try pool.mkAnd(a, b), try pool.mkNot(a));
    const s = try toString(std.testing.allocator, &pool, e);
    defer std.testing.allocator.free(s);
    try std.testing.expect(std.mem.indexOf(u8, s, "a") != null);
}
