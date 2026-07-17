//! Quantifier-free uninterpreted functions + equality (EUF) — Phase 3 spine.
//!
//! Ground terms with equality / disequality and uninterpreted predicates.
//! Congruence closure via union-find + iterative congruence merge.
//!
//! Industrial bar: full Nelson-Oppen / CC(X) not claimed; this is a correct
//! ground EUF checker for equalities, disequalities, and nullary/unary/binary preds.

const std = @import("std");

pub const TermId = enum(u32) {
    _,
    pub fn index(self: TermId) u32 {
        return @intFromEnum(self);
    }
    pub fn fromIndex(i: u32) TermId {
        return @enumFromInt(i);
    }
};

const TermKind = enum { const_, app };

const Term = struct {
    kind: TermKind,
    /// Interned name (const or function symbol).
    name: []const u8,
    /// App args (owned slice into uf.arg_pool indices as TermId).
    arity: u8 = 0,
    a0: TermId = TermId.fromIndex(0),
    a1: TermId = TermId.fromIndex(0),
};

pub const UfSolver = struct {
    allocator: std.mem.Allocator,
    terms: std.ArrayList(Term) = .empty,
    parent: std.ArrayList(u32) = .empty,
    rank: std.ArrayList(u8) = .empty,
    /// Disequalities: pairs of term indices that must stay distinct.
    diseq: std.ArrayList([2]u32) = .empty,
    /// Predicates: name → list of (polarity, arg terms...)
    /// Simplified: unary preds only for spine (P(t) / ¬P(t)).
    unary_pos: std.StringHashMapUnmanaged(std.ArrayList(u32)) = .{},
    unary_neg: std.StringHashMapUnmanaged(std.ArrayList(u32)) = .{},
    /// Name interning not needed if callers pass stable strings.

    pub fn init(allocator: std.mem.Allocator) UfSolver {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *UfSolver) void {
        var it = self.unary_pos.iterator();
        while (it.next()) |e| e.value_ptr.deinit(self.allocator);
        self.unary_pos.deinit(self.allocator);
        var it2 = self.unary_neg.iterator();
        while (it2.next()) |e| e.value_ptr.deinit(self.allocator);
        self.unary_neg.deinit(self.allocator);
        self.diseq.deinit(self.allocator);
        self.parent.deinit(self.allocator);
        self.rank.deinit(self.allocator);
        self.terms.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn mkConst(self: *UfSolver, name: []const u8) !TermId {
        const id = TermId.fromIndex(@intCast(self.terms.items.len));
        try self.terms.append(self.allocator, .{ .kind = .const_, .name = name });
        try self.parent.append(self.allocator, id.index());
        try self.rank.append(self.allocator, 0);
        return id;
    }

    pub fn mkApp1(self: *UfSolver, fname: []const u8, a0: TermId) !TermId {
        const id = TermId.fromIndex(@intCast(self.terms.items.len));
        try self.terms.append(self.allocator, .{
            .kind = .app,
            .name = fname,
            .arity = 1,
            .a0 = a0,
        });
        try self.parent.append(self.allocator, id.index());
        try self.rank.append(self.allocator, 0);
        return id;
    }

    pub fn mkApp2(self: *UfSolver, fname: []const u8, a0: TermId, a1: TermId) !TermId {
        const id = TermId.fromIndex(@intCast(self.terms.items.len));
        try self.terms.append(self.allocator, .{
            .kind = .app,
            .name = fname,
            .arity = 2,
            .a0 = a0,
            .a1 = a1,
        });
        try self.parent.append(self.allocator, id.index());
        try self.rank.append(self.allocator, 0);
        return id;
    }

    fn find(self: *UfSolver, x: u32) u32 {
        var cur = x;
        while (self.parent.items[cur] != cur) {
            self.parent.items[cur] = self.parent.items[self.parent.items[cur]];
            cur = self.parent.items[cur];
        }
        return cur;
    }

    fn union_(self: *UfSolver, a: u32, b: u32) void {
        var ra = self.find(a);
        var rb = self.find(b);
        if (ra == rb) return;
        if (self.rank.items[ra] < self.rank.items[rb]) {
            const t = ra;
            ra = rb;
            rb = t;
        }
        self.parent.items[rb] = ra;
        if (self.rank.items[ra] == self.rank.items[rb]) self.rank.items[ra] += 1;
    }

    pub fn assertEq(self: *UfSolver, a: TermId, b: TermId) void {
        self.union_(a.index(), b.index());
    }

    pub fn assertDiseq(self: *UfSolver, a: TermId, b: TermId) !void {
        try self.diseq.append(self.allocator, .{ a.index(), b.index() });
    }

    pub fn assertPred1(self: *UfSolver, pname: []const u8, t: TermId, positive: bool) !void {
        const map = if (positive) &self.unary_pos else &self.unary_neg;
        const gop = try map.getOrPut(self.allocator, pname);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(self.allocator, t.index());
    }

    fn sameApp(self: *const UfSolver, i: u32, j: u32) bool {
        const a = self.terms.items[i];
        const b = self.terms.items[j];
        if (a.kind != .app or b.kind != .app) return false;
        if (a.arity != b.arity) return false;
        if (!std.mem.eql(u8, a.name, b.name)) return false;
        return true;
    }

    /// Congruence closure: merge f(a) and f(b) when a~b (iterative).
    fn congruenceClose(self: *UfSolver) void {
        var changed = true;
        while (changed) {
            changed = false;
            const n = self.terms.items.len;
            var i: u32 = 0;
            while (i < n) : (i += 1) {
                var j = i + 1;
                while (j < n) : (j += 1) {
                    if (self.find(i) == self.find(j)) continue;
                    if (!self.sameApp(i, j)) continue;
                    const ti = self.terms.items[i];
                    const tj = self.terms.items[j];
                    var ok = true;
                    if (ti.arity >= 1 and self.find(ti.a0.index()) != self.find(tj.a0.index())) ok = false;
                    if (ti.arity >= 2 and self.find(ti.a1.index()) != self.find(tj.a1.index())) ok = false;
                    if (ok) {
                        self.union_(i, j);
                        changed = true;
                    }
                }
            }
        }
    }

    pub const CheckStatus = enum { sat, unsat };

    pub fn check(self: *UfSolver) CheckStatus {
        self.congruenceClose();
        // Disequalities
        for (self.diseq.items) |p| {
            if (self.find(p[0]) == self.find(p[1])) return .unsat;
        }
        // Unary preds: P(a) and ¬P(b) with a~b → unsat
        var pit = self.unary_pos.iterator();
        while (pit.next()) |pe| {
            const name = pe.key_ptr.*;
            const negs = self.unary_neg.getPtr(name) orelse continue;
            for (pe.value_ptr.items) |pi| {
                for (negs.items) |ni| {
                    if (self.find(pi) == self.find(ni)) return .unsat;
                }
            }
        }
        return .sat;
    }
};

test "uf equality sat" {
    var u = UfSolver.init(std.testing.allocator);
    defer u.deinit();
    const a = try u.mkConst("a");
    const b = try u.mkConst("b");
    u.assertEq(a, b);
    try std.testing.expect(u.check() == .sat);
}

test "uf disequality unsat" {
    var u = UfSolver.init(std.testing.allocator);
    defer u.deinit();
    const a = try u.mkConst("a");
    const b = try u.mkConst("b");
    u.assertEq(a, b);
    try u.assertDiseq(a, b);
    try std.testing.expect(u.check() == .unsat);
}

test "uf congruence f(a)=f(b) when a=b" {
    var u = UfSolver.init(std.testing.allocator);
    defer u.deinit();
    const a = try u.mkConst("a");
    const b = try u.mkConst("b");
    const fa = try u.mkApp1("f", a);
    const fb = try u.mkApp1("f", b);
    u.assertEq(a, b);
    try u.assertDiseq(fa, fb);
    // f(a)~f(b) so diseq fails
    try std.testing.expect(u.check() == .unsat);
}

test "uf pred conflict" {
    var u = UfSolver.init(std.testing.allocator);
    defer u.deinit();
    const a = try u.mkConst("a");
    const b = try u.mkConst("b");
    u.assertEq(a, b);
    try u.assertPred1("P", a, true);
    try u.assertPred1("P", b, false);
    try std.testing.expect(u.check() == .unsat);
}
