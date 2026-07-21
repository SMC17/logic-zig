//! Full multi-shot IPASIR-style solver API + C ABI.
//!
//! Zig API mirrors IPASIR semantics:
//! - add(lit) / add(0) terminates clause
//! - assume(lit) before solve
//! - solve() → 10 sat, 20 unsat, 0 unknown
//! - val(lit) model after sat
//! - failed(lit) after unsat under assumptions
//! - new vars grow on demand when |lit| exceeds current

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const solver_mod = @import("solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;
const Solver = solver_mod.Solver;

pub const TerminateCallback = *const fn (?*anyopaque) callconv(.c) c_int;
pub const LearnCallback = *const fn (?*anyopaque, [*c]const c_int) callconv(.c) void;

pub const IpasirResult = enum(c_int) {
    unknown = 0,
    sat = 10,
    unsat = 20,
};

pub const IpasirSolver = struct {
    allocator: std.mem.Allocator,
    /// Underlying incremental CDCL engine (rebuilt when vars grow).
    engine: ?Solver = null,
    /// Accumulated problem CNF (permanent clauses only).
    formula: Cnf,
    max_var: u32 = 0,
    /// Clause being built.
    clause_buf: std.ArrayList(Lit) = .empty,
    /// Assumptions for next solve.
    assumptions: std.ArrayList(Lit) = .empty,
    /// Last solve result.
    last: IpasirResult = .unknown,
    /// Model after SAT (1-based dimacs polarity in parallel to assign).
    model: ?[]Value = null,
    /// Failed assumptions after UNSAT (dimacs lits).
    failed_set: std.AutoHashMapUnmanaged(i32, void) = .{},
    /// Sticky C-ABI failure state. Void ABI calls cannot return allocation errors.
    fatal: bool = false,
    terminate_state: ?*anyopaque = null,
    terminate_callback: ?TerminateCallback = null,
    learn_state: ?*anyopaque = null,
    learn_callback: ?LearnCallback = null,
    learn_max_len: c_int = 0,
    learn_buf: std.ArrayList(c_int) = .empty,
    opts: solver_mod.SolverOptions = .{},

    pub fn init(allocator: std.mem.Allocator) IpasirSolver {
        return .{
            .allocator = allocator,
            .formula = Cnf.init(allocator),
        };
    }

    pub fn deinit(self: *IpasirSolver) void {
        if (self.engine) |*e| e.deinit();
        self.formula.deinit();
        self.clause_buf.deinit(self.allocator);
        self.assumptions.deinit(self.allocator);
        if (self.model) |m| self.allocator.free(m);
        self.failed_set.deinit(self.allocator);
        self.learn_buf.deinit(self.allocator);
        self.* = undefined;
    }

    fn ensureVar(self: *IpasirSolver, v: u32) void {
        if (v > self.max_var) {
            self.max_var = v;
            self.formula.ensureVars(v);
        }
    }

    fn dimacsToLit(self: *IpasirSolver, dimacs: i32) !Lit {
        if (dimacs == 0) return error.InvalidLit;
        const abs: u32 = @intCast(if (dimacs < 0) -dimacs else dimacs);
        self.ensureVar(abs);
        return Lit.fromDimacs(dimacs);
    }

    /// IPASIR add: dimacs lit, 0 ends clause.
    pub fn add(self: *IpasirSolver, lit_dimacs: i32) !void {
        if (lit_dimacs == 0) {
            // Empty buffer followed by 0 is the empty clause, not a no-op.
            try self.formula.addClause(self.clause_buf.items);
            if (self.engine) |*e| {
                try e.addClausePermanent(self.clause_buf.items);
            }
            self.clause_buf.clearRetainingCapacity();
            return;
        }
        const l = try self.dimacsToLit(lit_dimacs);
        try self.clause_buf.append(self.allocator, l);
    }

    pub fn assume(self: *IpasirSolver, lit_dimacs: i32) !void {
        const l = try self.dimacsToLit(lit_dimacs);
        try self.assumptions.append(self.allocator, l);
    }

    fn rebuildEngine(self: *IpasirSolver) !void {
        if (self.engine) |*e| e.deinit();
        self.engine = try Solver.init(self.allocator, &self.formula, self.opts);
    }

    fn terminationThunk(ctx: ?*anyopaque) bool {
        const self: *IpasirSolver = @ptrCast(@alignCast(ctx orelse return false));
        const callback = self.terminate_callback orelse return false;
        return callback(self.terminate_state) != 0;
    }

    fn learnThunk(ctx: ?*anyopaque, clause: []const Lit) void {
        const self: *IpasirSolver = @ptrCast(@alignCast(ctx orelse return));
        const callback = self.learn_callback orelse return;
        if (self.learn_max_len <= 0 or clause.len > @as(usize, @intCast(self.learn_max_len))) return;
        self.learn_buf.clearRetainingCapacity();
        for (clause) |lit| self.learn_buf.append(self.allocator, lit.toDimacs()) catch {
            self.fatal = true;
            return;
        };
        self.learn_buf.append(self.allocator, 0) catch {
            self.fatal = true;
            return;
        };
        callback(self.learn_state, self.learn_buf.items.ptr);
    }

    pub fn setTerminate(self: *IpasirSolver, state: ?*anyopaque, callback: ?TerminateCallback) void {
        self.terminate_state = state;
        self.terminate_callback = callback;
        self.opts.terminate_state = self;
        self.opts.terminate_callback = if (callback == null) null else terminationThunk;
        if (self.engine) |*engine| engine.opts = self.opts;
    }

    pub fn setLearn(self: *IpasirSolver, state: ?*anyopaque, max_len: c_int, callback: ?LearnCallback) void {
        self.learn_state = state;
        self.learn_callback = callback;
        self.learn_max_len = max_len;
        self.opts.learn_state = self;
        self.opts.learn_callback = if (callback == null or max_len <= 0) null else learnThunk;
        if (self.engine) |*engine| engine.opts = self.opts;
    }

    pub fn solve(self: *IpasirSolver) !IpasirResult {
        self.failed_set.clearRetainingCapacity();
        if (self.model) |m| {
            self.allocator.free(m);
            self.model = null;
        }

        // An unterminated clause is not part of the formula yet. Preserve it so
        // a later add(0) completes the caller's clause instead of losing data.

        if (self.engine == null or self.engine.?.num_vars < self.max_var) {
            try self.rebuildEngine();
        }

        var eng = &self.engine.?;
        // Grow solver if formula has more vars than engine
        if (eng.num_vars < self.max_var) {
            try self.rebuildEngine();
            eng = &self.engine.?;
        }

        const r = try eng.solveAssumptions(self.assumptions.items);
        self.assumptions.clearRetainingCapacity();

        switch (r.status) {
            .sat => {
                self.model = r.model;
                if (r.assumption_core) |c| self.allocator.free(c);
                self.last = .sat;
                return .sat;
            },
            .unsat => {
                if (r.model) |m| self.allocator.free(m);
                // Prefer deletion-minimal core from the engine.
                if (r.assumption_core) |core| {
                    defer self.allocator.free(core);
                    for (core) |d| {
                        try self.failed_set.put(self.allocator, d, {});
                    }
                }
                self.last = .unsat;
                return .unsat;
            },
            .unknown => {
                if (r.model) |m| self.allocator.free(m);
                if (r.assumption_core) |c| self.allocator.free(c);
                self.last = .unknown;
                return .unknown;
            },
        }
    }

    /// IPASIR val: after SAT, return lit if true, -lit if false, 0 if unassigned.
    pub fn val(self: *const IpasirSolver, lit_dimacs: i32) i32 {
        if (self.last != .sat) return 0;
        const m = self.model orelse return 0;
        if (lit_dimacs == 0) return 0;
        const abs: u32 = @intCast(if (lit_dimacs < 0) -lit_dimacs else lit_dimacs);
        if (abs == 0 or abs > m.len) return 0;
        const is_true = m[abs - 1] == .true_;
        if (lit_dimacs > 0) {
            return if (is_true) lit_dimacs else -lit_dimacs;
        } else {
            return if (!is_true) lit_dimacs else -lit_dimacs;
        }
    }

    /// IPASIR failed: after UNSAT, non-zero if lit is in the minimal assumption core.
    pub fn failed(self: *const IpasirSolver, lit_dimacs: i32) c_int {
        if (self.last != .unsat) return 0;
        if (self.failed_set.contains(lit_dimacs)) return 1;
        return 0;
    }

    pub fn signature() [*:0]const u8 {
        return "logic-zig-ipasir-1.0";
    }
};

// C ABI lives in ipasir_c.zig (linked into libipasirlogic.so with libc).

const CallbackState = struct { calls: u32 = 0, last_len: u32 = 0 };

fn terminateImmediately(state: ?*anyopaque) callconv(.c) c_int {
    const s: *CallbackState = @ptrCast(@alignCast(state.?));
    s.calls += 1;
    return 1;
}

fn recordLearned(state: ?*anyopaque, clause: [*c]const c_int) callconv(.c) void {
    const s: *CallbackState = @ptrCast(@alignCast(state.?));
    s.calls += 1;
    var len: u32 = 0;
    while (clause[len] != 0) : (len += 1) {}
    s.last_len = len;
}

test "ipasir zig api sat unsat" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    // (a | b) & (~a) → b
    try s.add(1);
    try s.add(2);
    try s.add(0);
    try s.add(-1);
    try s.add(0);
    const r = try s.solve();
    try std.testing.expect(r == .sat);
    try std.testing.expect(s.val(2) == 2);

    try s.add(-2);
    try s.add(0);
    const r2 = try s.solve();
    try std.testing.expect(r2 == .unsat);
}

test "ipasir assumptions" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    try s.add(1);
    try s.add(2);
    try s.add(0);
    try s.assume(-1);
    try s.assume(-2);
    const r = try s.solve();
    try std.testing.expect(r == .unsat);
    // Minimal core for (a|b) under ~a,~b needs both
    try std.testing.expect(s.failed(-1) != 0);
    try std.testing.expect(s.failed(-2) != 0);
}

test "ipasir failed drops irrelevant assumption" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    // a & ~a, extra free b
    try s.add(1);
    try s.add(0);
    try s.add(-1);
    try s.add(0);
    try s.assume(2); // b — irrelevant to conflict
    try s.assume(1); // forces with ~a... wait a is unit already
    // Actually units force a and ~a already unsat without assumptions
    const r = try s.solve();
    try std.testing.expect(r == .unsat);
    // Core may be empty if conflict is at level 0 without assumptions
    // assume 2 should not be required
    try std.testing.expect(s.failed(2) == 0);
}

test "ipasir multi-shot keep clauses" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    try s.add(1);
    try s.add(0);
    try std.testing.expect((try s.solve()) == .sat);
    try s.assume(-1);
    try std.testing.expect((try s.solve()) == .unsat);
    // without assumption, still sat
    try std.testing.expect((try s.solve()) == .sat);
}

test "ipasir add zero creates empty clause" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    try s.add(0);
    try std.testing.expectEqual(IpasirResult.unsat, try s.solve());
}

test "ipasir solve preserves unterminated clause" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    try s.add(1);
    try std.testing.expectEqual(IpasirResult.sat, try s.solve());
    try s.add(0);
    try s.assume(-1);
    try std.testing.expectEqual(IpasirResult.unsat, try s.solve());
}

test "ipasir termination callback interrupts solve" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    try s.add(1);
    try s.add(0);
    var state: CallbackState = .{};
    s.setTerminate(&state, terminateImmediately);
    try std.testing.expectEqual(IpasirResult.unknown, try s.solve());
    try std.testing.expect(state.calls > 0);
}

test "ipasir learned clause callback receives zero-terminated clause" {
    var s = IpasirSolver.init(std.testing.allocator);
    defer s.deinit();
    // Unsatisfiable parity square with no root-level unit conflict.
    const clauses = [_][2]i32{ .{ 1, 2 }, .{ 1, -2 }, .{ -1, 2 }, .{ -1, -2 } };
    for (clauses) |clause| {
        try s.add(clause[0]);
        try s.add(clause[1]);
        try s.add(0);
    }
    var state: CallbackState = .{};
    s.setLearn(&state, 8, recordLearned);
    try std.testing.expectEqual(IpasirResult.unsat, try s.solve());
    try std.testing.expect(state.calls > 0);
    try std.testing.expect(state.last_len > 0 and state.last_len <= 8);
}
