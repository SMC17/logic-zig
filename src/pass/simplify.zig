//! Bottom-up algebraic simplification (rebuilds via smart constructors).

const std = @import("std");
const expr_mod = @import("../ir/expr.zig");
const ExprPool = expr_mod.ExprPool;
const ExprId = expr_mod.ExprId;

/// Rebuild expression using smart constructors (constant fold, absorb, etc.).
pub fn simplify(pool: *ExprPool, id: ExprId) !ExprId {
    return switch (pool.tag(id)) {
        .false_, .true_, .var_ => id,
        .not => try pool.mkNot(try simplify(pool, pool.child(id))),
        .and_ => try pool.mkAnd(
            try simplify(pool, pool.left(id)),
            try simplify(pool, pool.right(id)),
        ),
        .or_ => try pool.mkOr(
            try simplify(pool, pool.left(id)),
            try simplify(pool, pool.right(id)),
        ),
        .xor => try pool.mkXor(
            try simplify(pool, pool.left(id)),
            try simplify(pool, pool.right(id)),
        ),
        .implies => try pool.mkImplies(
            try simplify(pool, pool.left(id)),
            try simplify(pool, pool.right(id)),
        ),
        .iff => try pool.mkIff(
            try simplify(pool, pool.left(id)),
            try simplify(pool, pool.right(id)),
        ),
    };
}

test "simplify tautology fragment" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkVarNamed("a");
    const e = try pool.mkOr(a, try pool.mkNot(a));
    const s = try simplify(&pool, e);
    try std.testing.expect(s == .true_);
}
