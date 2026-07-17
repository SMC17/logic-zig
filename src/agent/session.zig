//! Agent-oriented multishot SAT session — warm engine, cores, optional proofs.
//! Target niche: thousands of assumption queries without process spawn.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");
const profiles = @import("../profile/profiles.zig");
const drat_mod = @import("../sat/drat.zig");

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
    model: ?[]Value = null,
    /// When session.proof enabled and UNSAT — owned; free with deinitProof.
    proof: ?drat_mod.Proof = null,

    pub fn deinit(self: *QueryResult, allocator: std.mem.Allocator) void {
        if (self.model) |m| {
            allocator.free(m);
            self.model = null;
        }
        if (self.core) |c| {
            allocator.free(c);
            self.core = null;
        }
        if (self.proof) |*p| {
            p.deinit();
            self.proof = null;
        }
    }
};

pub const Session = struct {
    allocator: std.mem.Allocator,
    formula: Cnf,
    engine: ?Solver = null,
    queries: u32 = 0,
    total_conflicts: u64 = 0,
    sat_count: u32 = 0,
    unsat_count: u32 = 0,
    /// Enable RUP proof logging on queries (slower; for cert path).
    enable_proof: bool = false,
    opts: solver_mod.SolverOptions = .{},

    pub fn init(allocator: std.mem.Allocator) Session {
        const prof = profiles.get(.agent);
        return .{
            .allocator = allocator,
            .formula = Cnf.init(allocator),
            .opts = prof.solver,
        };
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

    pub fn addDimacsClause(self: *Session, lits: []const i32) !void {
        var buf: std.ArrayList(Lit) = .empty;
        defer buf.deinit(self.allocator);
        for (lits) |d| {
            if (d == 0) break;
            const abs: u32 = @intCast(if (d < 0) -d else d);
            self.ensureVars(abs);
            try buf.append(self.allocator, Lit.fromDimacs(d));
        }
        try self.addClause(buf.items);
    }

    pub fn ensureVars(self: *Session, n: u32) void {
        self.formula.ensureVars(n);
    }

    fn ensureEngine(self: *Session) !void {
        if (self.engine != null) return;
        var opts = self.opts;
        opts.proof = self.enable_proof;
        self.opts.proof = self.enable_proof;
        self.engine = try Solver.init(self.allocator, &self.formula, opts);
    }

    /// Solve under assumptions; keeps learned clauses.
    pub fn query(self: *Session, assumptions: []const Lit) !QueryResult {
        // Rebuild if proof flag flipped after engine create
        if (self.engine != null and self.enable_proof != self.opts.proof) {
            self.engine.?.deinit();
            self.engine = null;
        }
        try self.ensureEngine();
        const r = try self.engine.?.solveAssumptions(assumptions);
        self.queries += 1;
        self.total_conflicts += r.conflicts;
        switch (r.status) {
            .sat => self.sat_count += 1,
            .unsat => self.unsat_count += 1,
            .unknown => {},
        }
        return .{
            .status = r.status,
            .conflicts = r.conflicts,
            .core = r.assumption_core,
            .core_unique = r.assumption_core_unique,
            .model = r.model,
            .proof = r.proof,
        };
    }

    pub fn queryDimacs(self: *Session, assumptions: []const i32) !QueryResult {
        var buf: std.ArrayList(Lit) = .empty;
        defer buf.deinit(self.allocator);
        for (assumptions) |d| {
            if (d == 0) continue;
            const abs: u32 = @intCast(if (d < 0) -d else d);
            self.ensureVars(abs);
            try buf.append(self.allocator, Lit.fromDimacs(d));
        }
        return self.query(buf.items);
    }

    /// Stress: N random assumption queries on a fixed base formula.
    pub fn stress(
        self: *Session,
        n_queries: u32,
        n_vars: u32,
        seed: u64,
    ) !struct { queries: u32, sat: u32, unsat: u32, conflicts: u64 } {
        self.ensureVars(n_vars);
        // Base: dense random 3-CNF
        var prng = std.Random.DefaultPrng.init(seed);
        const rng = prng.random();
        var c: u32 = 0;
        while (c < n_vars * 3) : (c += 1) {
            var cl: [3]Lit = undefined;
            var k: u32 = 0;
            while (k < 3) : (k += 1) {
                cl[k] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n_vars)), rng.boolean());
            }
            try self.addClause(&cl);
        }
        var i: u32 = 0;
        while (i < n_queries) : (i += 1) {
            // 0–3 random assumptions
            var ass: std.ArrayList(Lit) = .empty;
            defer ass.deinit(self.allocator);
            const na = rng.intRangeLessThan(u32, 0, 4);
            var j: u32 = 0;
            while (j < na) : (j += 1) {
                try ass.append(self.allocator, Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n_vars)), rng.boolean()));
            }
            var r = try self.query(ass.items);
            r.deinit(self.allocator);
        }
        return .{
            .queries = self.queries,
            .sat = self.sat_count,
            .unsat = self.unsat_count,
            .conflicts = self.total_conflicts,
        };
    }
};

const WarmCold = struct {
    warm_conflicts: u64,
    cold_conflicts: u64,
    warm_queries: u32,
    mode: []const u8 = "random",
};

fn runWarmColdSequences(
    allocator: std.mem.Allocator,
    formula: *const Cnf,
    sequences: []const []Lit,
    mode: []const u8,
) !WarmCold {
    var warm = Session.init(allocator);
    defer warm.deinit();
    warm.ensureVars(formula.num_vars);
    var ci: u32 = 0;
    while (ci < formula.numClauses()) : (ci += 1) {
        try warm.addClause(formula.clauseSlice(cnf_mod.ClauseId.fromIndex(ci)));
    }
    for (sequences) |ass| {
        var r = try warm.query(ass);
        r.deinit(allocator);
    }

    var cold_conf: u64 = 0;
    for (sequences) |ass| {
        var eng = try Solver.init(allocator, &formula.*, profiles.get(.agent).solver);
        defer eng.deinit();
        const r = try eng.solveAssumptions(ass);
        cold_conf += r.conflicts;
        if (r.model) |m| allocator.free(m);
        if (r.assumption_core) |core| allocator.free(core);
        if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        }
    }
    return .{
        .warm_conflicts = warm.total_conflicts,
        .cold_conflicts = cold_conf,
        .warm_queries = warm.queries,
        .mode = mode,
    };
}

/// Cold vs warm: **random** assumptions (can thrash warm with junk lemmas).
pub fn compareWarmCold(
    allocator: std.mem.Allocator,
    n_vars: u32,
    n_queries: u32,
    seed: u64,
) !WarmCold {
    var prng = std.Random.DefaultPrng.init(seed);
    const rng = prng.random();

    var formula = Cnf.init(allocator);
    defer formula.deinit();
    formula.ensureVars(n_vars);
    var c: u32 = 0;
    while (c < n_vars * 4) : (c += 1) {
        var cl: [3]Lit = undefined;
        var k: u32 = 0;
        while (k < 3) : (k += 1) {
            cl[k] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n_vars)), rng.boolean());
        }
        try formula.addClause(&cl);
    }

    var sequences: std.ArrayList([]Lit) = .empty;
    defer {
        for (sequences.items) |s| allocator.free(s);
        sequences.deinit(allocator);
    }
    var i: u32 = 0;
    while (i < n_queries) : (i += 1) {
        const na = rng.intRangeLessThan(u32, 1, 4);
        const ass = try allocator.alloc(Lit, na);
        var j: u32 = 0;
        while (j < na) : (j += 1) {
            ass[j] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n_vars)), rng.boolean());
        }
        try sequences.append(allocator, ass);
    }
    return runWarmColdSequences(allocator, &formula, sequences.items, "random");
}

/// Structured agent workload: base (x0 ∨ x1 ∨ …) clauses + assumptions that
/// **grow a unit trail** on the same vars (related queries). Warm should win.
pub fn compareWarmColdStructured(
    allocator: std.mem.Allocator,
    n_vars: u32,
    n_queries: u32,
) !WarmCold {
    std.debug.assert(n_vars >= 4);
    var formula = Cnf.init(allocator);
    defer formula.deinit();
    formula.ensureVars(n_vars);
    // Horn-ish: (~xi ∨ x{i+1}) chain + (x0 ∨ x1 ∨ x2)
    try formula.addClause(&.{
        Lit.positive(Var.fromIndex(0)),
        Lit.positive(Var.fromIndex(1)),
        Lit.positive(Var.fromIndex(2)),
    });
    var i: u32 = 0;
    while (i + 1 < n_vars) : (i += 1) {
        try formula.addClause(&.{
            Lit.negative(Var.fromIndex(i)),
            Lit.positive(Var.fromIndex(i + 1)),
        });
    }
    // Extra redundant clauses to give learning room
    i = 0;
    while (i + 2 < n_vars) : (i += 1) {
        try formula.addClause(&.{
            Lit.negative(Var.fromIndex(i)),
            Lit.negative(Var.fromIndex(i + 1)),
            Lit.positive(Var.fromIndex(i + 2)),
        });
    }

    var sequences: std.ArrayList([]Lit) = .empty;
    defer {
        for (sequences.items) |s| allocator.free(s);
        sequences.deinit(allocator);
    }
    // Query k: assume ~x0, ~x1, ... for first (k % n_vars) then force conflict variants
    i = 0;
    while (i < n_queries) : (i += 1) {
        const depth = 1 + (i % (n_vars / 2));
        const ass = try allocator.alloc(Lit, depth);
        var j: u32 = 0;
        while (j < depth) : (j += 1) {
            // Growing prefix of negative assumptions — related refinements
            ass[j] = Lit.negative(Var.fromIndex(j));
        }
        try sequences.append(allocator, ass);
    }
    return runWarmColdSequences(allocator, &formula, sequences.items, "structured");
}

test "agent session multishot cores" {
    var s = Session.init(std.testing.allocator);
    defer s.deinit();
    s.ensureVars(2);
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try s.addClause(&.{ a, b });

    var r1 = try s.query(&.{ a.not(), b.not() });
    defer r1.deinit(std.testing.allocator);
    try std.testing.expect(r1.status == .unsat);
    try std.testing.expect(r1.core_unique);

    var r2 = try s.query(&.{a.not()});
    defer r2.deinit(std.testing.allocator);
    try std.testing.expect(r2.status == .sat);
    try std.testing.expect(s.queries == 2);
}

test "agent stress 200 queries" {
    var s = Session.init(std.testing.allocator);
    defer s.deinit();
    const st = try s.stress(200, 8, 0xA6E17);
    try std.testing.expect(st.queries == 200);
    try std.testing.expect(st.sat + st.unsat <= 200);
}

test "warm vs cold multishot runs" {
    const c = try compareWarmCold(std.testing.allocator, 6, 40, 0xC01D);
    try std.testing.expect(c.warm_queries == 40);
    try std.testing.expect(c.warm_conflicts < 10_000_000);
}

test "structured warm not worse than cold by huge margin" {
    const c = try compareWarmColdStructured(std.testing.allocator, 12, 60);
    try std.testing.expect(c.warm_queries == 60);
    try std.testing.expectEqualStrings("structured", c.mode);
    // Structured related assumptions: warm should be competitive (≤ 3× cold)
    if (c.cold_conflicts > 0) {
        try std.testing.expect(c.warm_conflicts <= c.cold_conflicts * 3 + 100);
    }
}
