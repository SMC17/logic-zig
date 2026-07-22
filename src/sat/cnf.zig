//! CNF clause database (flat lit storage).

const std = @import("std");
const lit_mod = @import("../core/lit.zig");
pub const Lit = lit_mod.Lit;
pub const Var = lit_mod.Var;
pub const Value = lit_mod.Value;

pub const ClauseId = enum(u32) {
    _,
    pub fn index(self: ClauseId) u32 {
        return @intFromEnum(self);
    }
    pub fn fromIndex(i: u32) ClauseId {
        return @enumFromInt(i);
    }
};

pub const ClauseRange = struct {
    start: u32,
    len: u32,
};

pub const Cnf = struct {
    allocator: std.mem.Allocator,
    num_vars: u32 = 0,
    lits: std.ArrayList(Lit) = .empty,
    clauses: std.ArrayList(ClauseRange) = .empty,

    pub fn init(allocator: std.mem.Allocator) Cnf {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Cnf) void {
        self.lits.deinit(self.allocator);
        self.clauses.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn ensureVars(self: *Cnf, n: u32) void {
        if (n > self.num_vars) self.num_vars = n;
    }

    pub fn addClause(self: *Cnf, clause: []const Lit) !void {
        // Always track vars mentioned (even if clause is dropped as tautology).
        for (clause) |l| {
            const vi = l.variable().index() + 1;
            if (vi > self.num_vars) self.num_vars = vi;
        }
        // Skip tautological clauses (contains l and ~l).
        var i: usize = 0;
        while (i < clause.len) : (i += 1) {
            var j = i + 1;
            while (j < clause.len) : (j += 1) {
                if (clause[i].not() == clause[j]) return;
            }
        }
        // Drop duplicate lits (stable unique).
        var tmp: std.ArrayList(Lit) = .empty;
        defer tmp.deinit(self.allocator);
        for (clause) |l| {
            var dup = false;
            for (tmp.items) |e| {
                if (e == l) {
                    dup = true;
                    break;
                }
            }
            if (!dup) try tmp.append(self.allocator, l);
        }
        if (tmp.items.len == 0) {
            // Empty clause after dedup — still represent unsat unit.
            const start: u32 = @intCast(self.lits.items.len);
            try self.clauses.append(self.allocator, .{ .start = start, .len = 0 });
            return;
        }
        const start: u32 = @intCast(self.lits.items.len);
        try self.lits.appendSlice(self.allocator, tmp.items);
        try self.clauses.append(self.allocator, .{
            .start = start,
            .len = @intCast(tmp.items.len),
        });
    }

    pub fn clauseSlice(self: *const Cnf, id: ClauseId) []const Lit {
        const r = self.clauses.items[id.index()];
        return self.lits.items[r.start .. r.start + r.len];
    }

    pub fn numClauses(self: *const Cnf) u32 {
        return @intCast(self.clauses.items.len);
    }

    /// Check whether assignment satisfies every clause. Partial assign: undef lit ignored;
    /// clause satisfied if some lit true; violated if all lits false; else undetermined.
    pub fn checkModel(self: *const Cnf, assign: []const Value) bool {
        std.debug.assert(assign.len >= self.num_vars);
        for (0..self.clauses.items.len) |ci| {
            const cl = self.clauseSlice(ClauseId.fromIndex(@intCast(ci)));
            var sat = false;
            for (cl) |l| {
                const v = lit_mod.evalLit(l, assign);
                if (v == .true_) {
                    sat = true;
                    break;
                }
                if (v == .undef) {
                    // Treat undef as not yet true — for total models should not happen.
                    sat = false;
                }
            }
            if (!sat) {
                // All defined and none true, or empty clause.
                var all_false = true;
                for (cl) |l| {
                    if (lit_mod.evalLit(l, assign) != .false_) {
                        all_false = false;
                        break;
                    }
                }
                if (cl.len == 0 or all_false) return false;
                // Has undef — incomplete; for total model check require all sat.
                return false;
            }
        }
        return true;
    }
};

test "cnf add and check" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ a, b });
    try cnf.addClause(&.{a.not()});
    var assign = [_]Value{ .false_, .true_ };
    try std.testing.expect(cnf.checkModel(&assign));
    assign[1] = .false_;
    try std.testing.expect(!cnf.checkModel(&assign));
}

test "cnf empty clause is unsat marker" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    try cnf.addClause(&.{});
    try std.testing.expect(cnf.numClauses() == 1);
    try std.testing.expect(cnf.clauseSlice(ClauseId.fromIndex(0)).len == 0);
    var assign = [_]Value{};
    try std.testing.expect(!cnf.checkModel(&assign));
}

test "cnf tautology dropped but vars counted" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const x = Lit.positive(Var.fromIndex(2));
    try cnf.addClause(&.{ x, x.not() });
    try std.testing.expect(cnf.numClauses() == 0);
    try std.testing.expect(cnf.num_vars == 3);
}

test "cnf duplicate lits collapsed" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const x = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{ x, x, x });
    try std.testing.expect(cnf.numClauses() == 1);
    try std.testing.expect(cnf.clauseSlice(ClauseId.fromIndex(0)).len == 1);
}
