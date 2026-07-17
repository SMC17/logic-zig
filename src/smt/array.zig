//! Array theory stub — Phase 3 residual.
//!
//! Honest status: **not** a full array decision procedure (no extensionality,
//! no general i≠j case completeness, not Z3/CVC5 parity).
//!
//! What exists: ground McCarthy **read-over-write** for the equal-index case,
//! encoded on top of UF:
//!   select(store(a, i, v), j)  with  i ~ j  ⇒  select ~ v
//!
//! Encoding: store(a,i,v) := `store(store1(a,i), v)` (binary apps only).
//!           select(a,i)  := `select(a, i)`.

const std = @import("std");
const uf_mod = @import("uf.zig");

pub const TermId = uf_mod.TermId;
pub const UfSolver = uf_mod.UfSolver;

/// Feature flag for api/capability consumers.
pub const supported_partial: bool = true; // equal-index read-over-write only
pub const full_array_theory: bool = false;
pub const reason_full: []const u8 = "full array extensionality / i≠j store chain not implemented";

const StoreRec = struct {
    /// Term id of store(store1(a,i), v)
    term: TermId,
    arr: TermId,
    idx: TermId,
    val: TermId,
};

const SelectRec = struct {
    term: TermId,
    arr: TermId,
    idx: TermId,
};

pub const ArraySolver = struct {
    allocator: std.mem.Allocator,
    uf: UfSolver,
    stores: std.ArrayList(StoreRec) = .empty,
    selects: std.ArrayList(SelectRec) = .empty,

    pub fn init(allocator: std.mem.Allocator) ArraySolver {
        return .{
            .allocator = allocator,
            .uf = UfSolver.init(allocator),
        };
    }

    pub fn deinit(self: *ArraySolver) void {
        self.stores.deinit(self.allocator);
        self.selects.deinit(self.allocator);
        self.uf.deinit();
        self.* = undefined;
    }

    pub fn mkConst(self: *ArraySolver, name: []const u8) !TermId {
        return self.uf.mkConst(name);
    }

    /// store(a, i, v) as nested binary apps.
    pub fn mkStore(self: *ArraySolver, arr: TermId, idx: TermId, val: TermId) !TermId {
        const mid = try self.uf.mkApp2("store1", arr, idx);
        const t = try self.uf.mkApp2("store", mid, val);
        try self.stores.append(self.allocator, .{
            .term = t,
            .arr = arr,
            .idx = idx,
            .val = val,
        });
        return t;
    }

    pub fn mkSelect(self: *ArraySolver, arr: TermId, idx: TermId) !TermId {
        const t = try self.uf.mkApp2("select", arr, idx);
        try self.selects.append(self.allocator, .{
            .term = t,
            .arr = arr,
            .idx = idx,
        });
        return t;
    }

    pub fn assertEq(self: *ArraySolver, a: TermId, b: TermId) void {
        self.uf.assertEq(a, b);
    }

    pub fn assertDiseq(self: *ArraySolver, a: TermId, b: TermId) !void {
        try self.uf.assertDiseq(a, b);
    }

    /// Apply read-over-write (equal index) to fixpoint, then UF check.
    fn applyReadOverWrite(self: *ArraySolver) void {
        var guard: u32 = 0;
        while (guard < 64) : (guard += 1) {
            self.uf.congruenceClose();
            var changed = false;
            for (self.stores.items) |st| {
                for (self.selects.items) |se| {
                    // select(arr_s, j) when arr_s ~ store(...) and j ~ st.idx → se ~ st.val
                    if (!self.uf.sameClass(se.arr, st.term)) continue;
                    if (!self.uf.sameClass(se.idx, st.idx)) continue;
                    if (!self.uf.sameClass(se.term, st.val)) {
                        self.uf.assertEq(se.term, st.val);
                        changed = true;
                    }
                }
            }
            if (!changed) break;
        }
    }

    pub const CheckStatus = enum { sat, unsat };

    pub fn check(self: *ArraySolver) CheckStatus {
        self.applyReadOverWrite();
        return switch (self.uf.check()) {
            .sat => .sat,
            .unsat => .unsat,
        };
    }
};

// ── tests ────────────────────────────────────────────────────────────

test "array select store same index equals value sat" {
    var a = ArraySolver.init(std.testing.allocator);
    defer a.deinit();
    const arr = try a.mkConst("A");
    const i = try a.mkConst("i");
    const v = try a.mkConst("v");
    const st = try a.mkStore(arr, i, v);
    const se = try a.mkSelect(st, i);
    a.assertEq(se, v);
    try std.testing.expect(a.check() == .sat);
}

test "array select store same index diseq unsat" {
    var a = ArraySolver.init(std.testing.allocator);
    defer a.deinit();
    const arr = try a.mkConst("A");
    const i = try a.mkConst("i");
    const v = try a.mkConst("v");
    const st = try a.mkStore(arr, i, v);
    const se = try a.mkSelect(st, i);
    try a.assertDiseq(se, v);
    try std.testing.expect(a.check() == .unsat);
}

test "array select store congruent indices unsat" {
    var a = ArraySolver.init(std.testing.allocator);
    defer a.deinit();
    const arr = try a.mkConst("A");
    const i = try a.mkConst("i");
    const j = try a.mkConst("j");
    const v = try a.mkConst("v");
    a.assertEq(i, j);
    const st = try a.mkStore(arr, i, v);
    const se = try a.mkSelect(st, j);
    try a.assertDiseq(se, v);
    try std.testing.expect(a.check() == .unsat);
}

test "array different index no forced eq (sat with diseq)" {
    // Honest residual: without i≠j axiom chain we do NOT force
    // select(store(a,i,v), j) = select(a,j). Disequality select≠v may stay sat.
    var a = ArraySolver.init(std.testing.allocator);
    defer a.deinit();
    const arr = try a.mkConst("A");
    const i = try a.mkConst("i");
    const j = try a.mkConst("j");
    const v = try a.mkConst("v");
    try a.assertDiseq(i, j);
    const st = try a.mkStore(arr, i, v);
    const se = try a.mkSelect(st, j);
    try a.assertDiseq(se, v);
    try std.testing.expect(a.check() == .sat);
}

test "array feature flags honest" {
    try std.testing.expect(supported_partial);
    try std.testing.expect(!full_array_theory);
}
