//! Negation normal form: push negation to atoms; eliminate implies/iff/xor.

const std = @import("std");
const expr_mod = @import("../ir/expr.zig");
const ExprPool = expr_mod.ExprPool;
const ExprId = expr_mod.ExprId;

/// Convert `id` to NNF in `pool` (may allocate new nodes).
pub fn toNnf(pool: *ExprPool, id: ExprId) !ExprId {
    return nnf(pool, id, false);
}

fn nnf(pool: *ExprPool, id: ExprId, neg: bool) !ExprId {
    switch (pool.tag(id)) {
        .false_ => return if (neg) pool.mkTrue() else pool.mkFalse(),
        .true_ => return if (neg) pool.mkFalse() else pool.mkTrue(),
        .var_ => {
            if (neg) return try pool.mkNot(id);
            return id;
        },
        .not => return nnf(pool, pool.child(id), !neg),
        .and_ => {
            const l = try nnf(pool, pool.left(id), neg);
            const r = try nnf(pool, pool.right(id), neg);
            if (neg) return try pool.mkOr(l, r);
            return try pool.mkAnd(l, r);
        },
        .or_ => {
            const l = try nnf(pool, pool.left(id), neg);
            const r = try nnf(pool, pool.right(id), neg);
            if (neg) return try pool.mkAnd(l, r);
            return try pool.mkOr(l, r);
        },
        .xor => {
            // a XOR b = (a|b) & !(a&b);  !(a XOR b) = a <-> b
            const a = pool.left(id);
            const b = pool.right(id);
            if (!neg) {
                const or_ab = try pool.mkOr(a, b);
                const and_ab = try pool.mkAnd(a, b);
                const nand = try pool.mkNot(and_ab);
                return nnf(pool, try pool.mkAnd(or_ab, nand), false);
            } else {
                return nnf(pool, try pool.mkIff(a, b), false);
            }
        },
        .implies => {
            // a -> b = !a | b;  !(a->b) = a & !b
            const a = pool.left(id);
            const b = pool.right(id);
            if (!neg) {
                return nnf(pool, try pool.mkOr(try pool.mkNot(a), b), false);
            } else {
                return nnf(pool, try pool.mkAnd(a, try pool.mkNot(b)), false);
            }
        },
        .iff => {
            // a <-> b = (a->b)&(b->a);  !(a<->b) = a XOR b
            const a = pool.left(id);
            const b = pool.right(id);
            if (!neg) {
                const ab = try pool.mkImplies(a, b);
                const ba = try pool.mkImplies(b, a);
                return nnf(pool, try pool.mkAnd(ab, ba), false);
            } else {
                return nnf(pool, try pool.mkXor(a, b), false);
            }
        },
    }
}

test "nnf pushes not" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkVarNamed("a");
    const b = try pool.mkVarNamed("b");
    const e = try pool.mkNot(try pool.mkAnd(a, b));
    const n = try toNnf(&pool, e);
    try std.testing.expect(pool.tag(n) == .or_);
}
