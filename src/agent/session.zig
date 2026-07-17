//! Agent-oriented multishot SAT session — keep engine warm across queries.
//!
//! Flagship path for `logic-agent`: permanent clauses + assumption queries
//! without process spawn overhead.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");
const profiles = @import("../profile/profiles.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;
const Solver = solver_mod.Solver;

pub const QueryResult = struct {
    status: solver_mod.SolveStatus,
    conflicts: u64 = 0,
    core: ?[]i32 = null,
    core_unique: bool = false,
    /// Caller frees model if non-null.
    model: ?[]Value = null,
};

pub const Session = struct {
    allocator: std.mem.Allocator,
    formula: Cnf,
    engine: ?Solver = null,
    queries: u32 = 0,
    total_conflicts: u64 = 0,

    pub fn init(allocator: std.mem.Allocator) Session {
        return .{ .allocator = allocator, .formula = Cnf.init(allocator) };
    }

    pub fn deinit(self: *Session) void {
        if (self.engine) |*e| e.deinit();
        self.formula.deinit();
        self.* = undefined;
    }

    pub fn addClause(self: *Session, lits: []const Lit) !void {
        try self.formula.addClause(lits);
        if (self.engine) |*e| try e.addClausePermanent(lits);
    }

    pub fn ensureVars(self: *Session, n: u32) void {
        self.formula.ensureVars(n);
    }

    fn ensureEngine(self: *Session) !void {
        if (self.engine != null) return;
        const prof = profiles.get(.agent);
        self.engine = try Solver.init(self.allocator, &self.formula, prof.solver);
    }

    /// Solve under assumptions; keeps learned clauses for next query.
    pub fn query(self: *Session, assumptions: []const Lit) !QueryResult {
        try self.ensureEngine();
        const r = try self.engine.?.solveAssumptions(assumptions);
        self.queries += 1;
        self.total_conflicts += r.conflicts;
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        return .{
            .status = r.status,
            .conflicts = r.conflicts,
            .core = r.assumption_core,
            .core_unique = r.assumption_core_unique,
            .model = r.model,
        };
    }
};

test "agent session multishot cores" {
    var s = Session.init(std.testing.allocator);
    defer s.deinit();
    s.ensureVars(2);
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try s.addClause(&.{ a, b });

    const r1 = try s.query(&.{ a.not(), b.not() });
    defer if (r1.model) |m| std.testing.allocator.free(m);
    defer if (r1.core) |c| std.testing.allocator.free(c);
    try std.testing.expect(r1.status == .unsat);
    try std.testing.expect(r1.core_unique);

    // Second query: sat under only ~a
    const r2 = try s.query(&.{a.not()});
    defer if (r2.model) |m| std.testing.allocator.free(m);
    defer if (r2.core) |c| std.testing.allocator.free(c);
    try std.testing.expect(r2.status == .sat);
    try std.testing.expect(s.queries == 2);
}
