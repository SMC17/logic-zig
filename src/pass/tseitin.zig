//! Tseitin transformation: formula → equisatisfiable CNF with aux variables.

const std = @import("std");
const expr_mod = @import("../ir/expr.zig");
const nnf_mod = @import("nnf.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");

const ExprPool = expr_mod.ExprPool;
const ExprId = expr_mod.ExprId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const TseitinResult = struct {
    cnf: Cnf,
    /// Literal that must be true for the original formula (top-level).
    root_lit: Lit,
    /// Number of original (named) variables before aux.
    num_orig_vars: u32,
};

/// Convert formula to CNF via Tseitin. Applies NNF first.
/// Fresh aux vars start at `pool.numVars()` and grow.
pub fn toCnf(pool: *ExprPool, formula: ExprId) !TseitinResult {
    const nnf = try nnf_mod.toNnf(pool, formula);
    var cnf = Cnf.init(pool.allocator);
    errdefer cnf.deinit();

    const num_orig = pool.numVars();
    cnf.ensureVars(num_orig);

    // Memo: ExprId.index → Lit encoding the subformula.
    var memo: std.AutoHashMapUnmanaged(u32, Lit) = .{};
    defer memo.deinit(pool.allocator);

    const root = try encode(pool, &cnf, nnf, &memo);
    // Force root true.
    try cnf.addClause(&.{root});

    return .{
        .cnf = cnf,
        .root_lit = root,
        .num_orig_vars = num_orig,
    };
}

fn encode(
    pool: *ExprPool,
    cnf: *Cnf,
    id: ExprId,
    memo: *std.AutoHashMapUnmanaged(u32, Lit),
) !Lit {
    if (memo.get(id.index())) |l| return l;

    const result: Lit = switch (pool.tag(id)) {
        .false_ => blk: {
            // Constant false: fresh var forced false, or use empty — use aux forced 0.
            const v = try freshAux(pool, cnf);
            try cnf.addClause(&.{Lit.negative(v)}); // ~v
            break :blk Lit.positive(v); // representing false is awkward; return v with v=false
        },
        .true_ => blk: {
            const v = try freshAux(pool, cnf);
            try cnf.addClause(&.{Lit.positive(v)});
            break :blk Lit.positive(v);
        },
        .var_ => Lit.positive(pool.varOf(id)),
        .not => blk: {
            const child = pool.child(id);
            if (pool.tag(child) == .var_) {
                break :blk Lit.negative(pool.varOf(child));
            }
            const inner = try encode(pool, cnf, child, memo);
            // For NNF, not only appears on vars — but if not, tseitin: x <-> ~inner
            const v = try freshAux(pool, cnf);
            const x = Lit.positive(v);
            // x -> ~inner  =>  ~x | ~inner
            try cnf.addClause(&.{ x.not(), inner.not() });
            // ~inner -> x  =>  inner | x
            try cnf.addClause(&.{ inner, x });
            break :blk x;
        },
        .and_ => blk: {
            const l = try encode(pool, cnf, pool.left(id), memo);
            const r = try encode(pool, cnf, pool.right(id), memo);
            const v = try freshAux(pool, cnf);
            const x = Lit.positive(v);
            // x -> l, x -> r, (l & r) -> x
            try cnf.addClause(&.{ x.not(), l });
            try cnf.addClause(&.{ x.not(), r });
            try cnf.addClause(&.{ l.not(), r.not(), x });
            break :blk x;
        },
        .or_ => blk: {
            const l = try encode(pool, cnf, pool.left(id), memo);
            const r = try encode(pool, cnf, pool.right(id), memo);
            const v = try freshAux(pool, cnf);
            const x = Lit.positive(v);
            // x -> l|r  => ~x|l|r
            try cnf.addClause(&.{ x.not(), l, r });
            // l -> x, r -> x
            try cnf.addClause(&.{ l.not(), x });
            try cnf.addClause(&.{ r.not(), x });
            break :blk x;
        },
        // After NNF these should not appear; handle defensively.
        .xor, .implies, .iff => {
            const renorm = try nnf_mod.toNnf(pool, id);
            return encode(pool, cnf, renorm, memo);
        },
    };

    try memo.put(pool.allocator, id.index(), result);
    // Ensure var count covers this lit.
    const need = result.variable().index() + 1;
    cnf.ensureVars(need);
    return result;
}

fn freshAux(pool: *ExprPool, cnf: *Cnf) !Var {
    // Create a named aux in the pool so numbering stays consistent.
    var buf: [32]u8 = undefined;
    const name = try std.fmt.bufPrint(&buf, "__t{d}", .{pool.numVars()});
    const eid = try pool.mkVarNamed(name);
    const v = pool.varOf(eid);
    cnf.ensureVars(v.index() + 1);
    return v;
}

test "tseitin simple sat" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const parse = @import("../parse/prop.zig");
    const e = try parse.parse(&pool, "a & b");
    var tr = try toCnf(&pool, e);
    defer tr.cnf.deinit();
    try std.testing.expect(tr.cnf.numClauses() >= 1);
    try std.testing.expect(tr.num_orig_vars == 2);
}
