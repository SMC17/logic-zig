//! RUP/DRAT-style proof log with clause additions and deletions.
//!
//! - `add` lines: clause must be RUP w.r.t. current DB
//! - `del` lines: remove a previously present clause (by literal multiset match)
//! - Final empty `add` establishes UNSAT

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;
const ClauseId = cnf_mod.ClauseId;

pub const LineKind = enum { add, del };

pub const Proof = struct {
    allocator: std.mem.Allocator,
    lits: std.ArrayList(Lit) = .empty,
    ranges: std.ArrayList(struct { start: u32, len: u32, kind: LineKind }) = .empty,
    /// Ordered temporary assumption context for this proof-producing solve.
    assumptions: std.ArrayList(Lit) = .empty,

    pub fn init(allocator: std.mem.Allocator) Proof {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Proof) void {
        self.lits.deinit(self.allocator);
        self.ranges.deinit(self.allocator);
        self.assumptions.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addClause(self: *Proof, clause: []const Lit) !void {
        const start: u32 = @intCast(self.lits.items.len);
        try self.lits.appendSlice(self.allocator, clause);
        try self.ranges.append(self.allocator, .{ .start = start, .len = @intCast(clause.len), .kind = .add });
    }

    pub fn delClause(self: *Proof, clause: []const Lit) !void {
        const start: u32 = @intCast(self.lits.items.len);
        try self.lits.appendSlice(self.allocator, clause);
        try self.ranges.append(self.allocator, .{ .start = start, .len = @intCast(clause.len), .kind = .del });
    }

    pub fn numLines(self: *const Proof) usize {
        return self.ranges.items.len;
    }

    pub fn setAssumptions(self: *Proof, assumptions: []const Lit) !void {
        self.assumptions.clearRetainingCapacity();
        try self.assumptions.appendSlice(self.allocator, assumptions);
    }

    pub fn numClauses(self: *const Proof) usize {
        return self.numLines();
    }

    pub fn clauseSlice(self: *const Proof, i: usize) []const Lit {
        const r = self.ranges.items[i];
        return self.lits.items[r.start .. r.start + r.len];
    }

    pub fn lineKind(self: *const Proof, i: usize) LineKind {
        return self.ranges.items[i].kind;
    }

    /// Verify proof: adds must be RUP; dels remove a matching live clause; last add empty for UNSAT.
    pub fn verifyRup(self: *const Proof, allocator: std.mem.Allocator, formula: *const Cnf) !bool {
        var db = Cnf.init(allocator);
        defer db.deinit();
        db.ensureVars(formula.num_vars);
        for (0..formula.numClauses()) |ci| {
            try db.addClause(formula.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
        }

        // Track live clause indices in db (soft: rebuild by re-adding active list).
        var live: std.ArrayList([]const Lit) = .empty;
        defer {
            for (live.items) |cl| allocator.free(cl);
            live.deinit(allocator);
        }
        for (0..db.numClauses()) |ci| {
            const cl = db.clauseSlice(ClauseId.fromIndex(@intCast(ci)));
            try live.append(allocator, try allocator.dupe(Lit, cl));
        }
        for (self.assumptions.items) |assumption| {
            try live.append(allocator, try allocator.dupe(Lit, &.{assumption}));
        }

        var last_was_empty_add = false;
        for (0..self.numLines()) |pi| {
            const cl = self.clauseSlice(pi);
            last_was_empty_add = false;
            switch (self.lineKind(pi)) {
                .add => {
                    if (!try isRupAgainstLive(allocator, live.items, formula.num_vars, cl)) return false;
                    try live.append(allocator, try allocator.dupe(Lit, cl));
                    if (cl.len == 0) last_was_empty_add = true;
                },
                .del => {
                    var found: ?usize = null;
                    for (live.items, 0..) |lc, i| {
                        if (sameClause(lc, cl)) {
                            found = i;
                            break;
                        }
                    }
                    if (found) |i| {
                        allocator.free(live.items[i]);
                        _ = live.orderedRemove(i);
                    } else {
                        return false; // deletion of unknown clause
                    }
                },
            }
        }
        if (self.numLines() == 0) return false;
        // Accept if last line is empty add (UNSAT certificate).
        const last = self.numLines() - 1;
        return self.lineKind(last) == .add and self.clauseSlice(last).len == 0 and last_was_empty_add;
    }

    pub fn writeDimacsLike(self: *const Proof, writer: *std.Io.Writer) !void {
        if (self.assumptions.items.len > 0) {
            try writer.writeAll("a ");
            for (self.assumptions.items) |assumption| try writer.print("{d} ", .{assumption.toDimacs()});
            try writer.writeAll("0\n");
        }
        for (0..self.numLines()) |i| {
            if (self.lineKind(i) == .del) try writer.writeAll("d ");
            const cl = self.clauseSlice(i);
            for (cl) |l| try writer.print("{d} ", .{l.toDimacs()});
            try writer.writeAll("0\n");
        }
    }
};

fn sameClause(a: []const Lit, b: []const Lit) bool {
    if (a.len != b.len) return false;
    // Multiset equality for small clauses.
    var used = [_]bool{false} ** 64;
    if (b.len > used.len) {
        // fallback O(n^2) without used array size limit
        for (a) |x| {
            var hit = false;
            for (b) |y| {
                if (x == y) {
                    hit = true;
                    break;
                }
            }
            if (!hit) return false;
        }
        return true;
    }
    for (a) |x| {
        var hit = false;
        for (b, 0..) |y, j| {
            if (!used[j] and x == y) {
                used[j] = true;
                hit = true;
                break;
            }
        }
        if (!hit) return false;
    }
    return true;
}

fn isRupAgainstLive(allocator: std.mem.Allocator, live: []const []const Lit, num_vars: u32, clause: []const Lit) !bool {
    var assign = try allocator.alloc(Value, num_vars);
    defer allocator.free(assign);
    @memset(assign, .undef);

    for (clause) |l| {
        const v = l.variable().index();
        if (v >= num_vars) continue;
        const want: Value = if (l.isNeg()) .true_ else .false_;
        if (assign[v] != .undef and assign[v] != want) return true;
        assign[v] = want;
    }

    var changed = true;
    while (changed) {
        changed = false;
        for (live) |cl| {
            if (cl.len == 0) return true;
            var undef_lit: ?Lit = null;
            var undef_count: u32 = 0;
            var sat = false;
            for (cl) |lit| {
                const val = lit_mod.evalLit(lit, assign);
                if (val == .true_) {
                    sat = true;
                    break;
                }
                if (val == .undef) {
                    undef_count += 1;
                    undef_lit = lit;
                }
            }
            if (sat) continue;
            if (undef_count == 0) return true;
            if (undef_count == 1) {
                const ul = undef_lit.?;
                const v = ul.variable().index();
                const want: Value = if (ul.isNeg()) .false_ else .true_;
                if (assign[v] == .undef) {
                    assign[v] = want;
                    changed = true;
                } else if (assign[v] != want) return true;
            }
        }
    }
    return false;
}

test "rup empty after units" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{a});
    try cnf.addClause(&.{a.not()});

    var proof = Proof.init(std.testing.allocator);
    defer proof.deinit();
    try proof.addClause(&.{});
    try std.testing.expect(try proof.verifyRup(std.testing.allocator, &cnf));
}

test "del line removes clause from live set" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    // Contradiction + redundant clause.
    try cnf.addClause(&.{a});
    try cnf.addClause(&.{a.not()});
    try cnf.addClause(&.{ a, b });

    var proof = Proof.init(std.testing.allocator);
    defer proof.deinit();
    // Delete redundant (a|b); live still has (a) and (~a).
    try proof.delClause(&.{ a, b });
    // Empty is RUP under contradiction.
    try proof.addClause(&.{});
    try std.testing.expect(try proof.verifyRup(std.testing.allocator, &cnf));

    // Deleting a clause that was never present must fail verification.
    var proof_bad = Proof.init(std.testing.allocator);
    defer proof_bad.deinit();
    try proof_bad.delClause(&.{b});
    try proof_bad.addClause(&.{});
    try std.testing.expect(!(try proof_bad.verifyRup(std.testing.allocator, &cnf)));
}

test "rup proof records assumption context" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{a});

    var proof = Proof.init(std.testing.allocator);
    defer proof.deinit();
    try proof.setAssumptions(&.{a.not()});
    try proof.addClause(&.{});
    try std.testing.expect(try proof.verifyRup(std.testing.allocator, &cnf));

    proof.assumptions.clearRetainingCapacity();
    try std.testing.expect(!(try proof.verifyRup(std.testing.allocator, &cnf)));
}
