//! logic-zig — propositional + sequential formal + FOL + IPASIR kernel.
//!
//! Proof level: unit-tested (see STATUS.md).

const std = @import("std");

pub const lit = @import("core/lit.zig");
pub const interner = @import("core/interner.zig");
pub const expr = @import("ir/expr.zig");
pub const pretty = @import("ir/pretty.zig");
pub const parse_prop = @import("parse/prop.zig");
pub const simplify_pass = @import("pass/simplify.zig");
pub const nnf = @import("pass/nnf.zig");
pub const tseitin = @import("pass/tseitin.zig");
pub const cnf = @import("sat/cnf.zig");
pub const solver = @import("sat/solver.zig");
pub const drat = @import("sat/drat.zig");
pub const fuzz = @import("sat/fuzz.zig");
pub const external = @import("sat/external.zig");
pub const ipasir = @import("sat/ipasir.zig");
pub const dimacs = @import("bridge/dimacs.zig");
pub const aiger = @import("bridge/aiger.zig");
pub const netlist = @import("circuit/netlist.zig");
pub const yosys_json = @import("circuit/yosys_json.zig");
pub const bmc = @import("circuit/bmc.zig");
pub const kinduction = @import("circuit/kinduction.zig");
pub const ic3 = @import("circuit/ic3.zig");
pub const pdr = @import("circuit/pdr.zig");
pub const ternary = @import("circuit/ternary.zig");
pub const justice = @import("circuit/justice.zig");
pub const kliveness = @import("circuit/kliveness.zig");
pub const aiger_write = @import("bridge/aiger_write.zig");
pub const fol_term = @import("fol/term.zig");
pub const unify = @import("fol/unify.zig");
pub const finite_model = @import("fol/finite_model.zig");
pub const finite_model_sat = @import("fol/finite_model_sat.zig");
pub const sat_track = @import("track/sat_track.zig");
pub const hwmcc_track = @import("track/hwmcc_track.zig");
pub const bench = @import("track/bench.zig");
pub const multishot_bench = @import("track/multishot_bench.zig");
pub const correctness_suite = @import("track/correctness_suite.zig");
pub const hwmcc_bench = @import("track/hwmcc_bench.zig");
pub const win_report = @import("track/win_report.zig");

pub const Lit = lit.Lit;
pub const Var = lit.Var;
pub const Value = lit.Value;
pub const ExprPool = expr.ExprPool;
pub const ExprId = expr.ExprId;
pub const Cnf = cnf.Cnf;
pub const Solver = solver.Solver;
pub const SolveResult = solver.SolveResult;
pub const SolveStatus = solver.SolveStatus;
pub const Netlist = netlist.Netlist;
pub const TermPool = fol_term.TermPool;
pub const FormulaPool = fol_term.FormulaPool;
pub const IpasirSolver = ipasir.IpasirSolver;

pub fn parse(pool: *ExprPool, source: []const u8) parse_prop.ParseError!ExprId {
    return parse_prop.parse(pool, source);
}

pub fn simplify(pool: *ExprPool, id: ExprId) !ExprId {
    return simplify_pass.simplify(pool, id);
}

pub fn toCnf(pool: *ExprPool, id: ExprId) !tseitin.TseitinResult {
    return tseitin.toCnf(pool, id);
}

pub fn solveCnf(allocator: std.mem.Allocator, formula: *const Cnf, opts: solver.SolverOptions) !SolveResult {
    return solver.solveCnf(allocator, formula, opts);
}

pub const FormulaQuery = struct {
    status: SolveStatus,
    model: ?[]Value = null,
    conflicts: u64 = 0,
    learned: u64 = 0,
};

pub fn satFormula(allocator: std.mem.Allocator, pool: *ExprPool, id: ExprId) !FormulaQuery {
    return satFormulaOpts(allocator, pool, id, .{});
}

pub fn satFormulaOpts(
    allocator: std.mem.Allocator,
    pool: *ExprPool,
    id: ExprId,
    opts: solver.SolverOptions,
) !FormulaQuery {
    var tr = try tseitin.toCnf(pool, id);
    defer tr.cnf.deinit();
    const r = try solver.solveCnf(allocator, &tr.cnf, opts);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    if (r.status != .sat) {
        return .{ .status = r.status, .conflicts = r.conflicts, .learned = r.learned };
    }
    const full = r.model.?;
    defer allocator.free(full);
    const n = tr.num_orig_vars;
    const model = try allocator.alloc(Value, n);
    errdefer allocator.free(model);
    @memcpy(model, full[0..n]);

    var assign = try allocator.alloc(Value, pool.numVars());
    defer allocator.free(assign);
    @memset(assign, .false_);
    const copy_n = @min(full.len, assign.len);
    @memcpy(assign[0..copy_n], full[0..copy_n]);
    if (pool.eval(id, assign) != .true_) {
        allocator.free(model);
        return error.ModelInvalid;
    }
    return .{ .status = .sat, .model = model, .conflicts = r.conflicts, .learned = r.learned };
}

pub fn isTautology(allocator: std.mem.Allocator, pool: *ExprPool, id: ExprId) !bool {
    const neg = try pool.mkNot(id);
    const q = try satFormula(allocator, pool, neg);
    defer if (q.model) |m| allocator.free(m);
    return q.status == .unsat;
}

pub fn areEquivalent(allocator: std.mem.Allocator, pool: *ExprPool, a: ExprId, b: ExprId) !bool {
    return isTautology(allocator, pool, try pool.mkIff(a, b));
}

pub const Error = error{
    ModelInvalid,
    ProofInvalid,
    PortMismatch,
    DomainTooLarge,
    TooManyPreds,
    TooManyArgs,
    Unbound,
};

test {
    std.testing.refAllDecls(@This());
    _ = lit;
    _ = interner;
    _ = expr;
    _ = pretty;
    _ = parse_prop;
    _ = simplify_pass;
    _ = nnf;
    _ = tseitin;
    _ = cnf;
    _ = solver;
    _ = drat;
    _ = fuzz;
    _ = external;
    _ = ipasir;
    _ = dimacs;
    _ = aiger;
    _ = netlist;
    _ = yosys_json;
    _ = bmc;
    _ = kinduction;
    _ = ic3;
    _ = pdr;
    _ = ternary;
    _ = justice;
    _ = kliveness;
    _ = aiger_write;
    _ = fol_term;
    _ = unify;
    _ = finite_model;
    _ = finite_model_sat;
    _ = sat_track;
    _ = hwmcc_track;
    _ = bench;
    _ = multishot_bench;
    _ = correctness_suite;
    _ = hwmcc_bench;
    _ = win_report;
}

test "end-to-end tautology a|!a" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    try std.testing.expect(try isTautology(std.testing.allocator, &pool, try parse(&pool, "a | !a")));
}
