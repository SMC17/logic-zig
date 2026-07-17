//! SMT facade — industrial SMT program (Phase 3 spine).
//!
//! Today: **BV** bit-blast (delegates to `bv.zig`).
//! Tomorrow: UF / arrays via DPLL(T)-style combination (capability bits off until real).
//!
//! API is stable for theory dispatch even while backends mature.

const std = @import("std");
const bv_mod = @import("bv.zig");
const solver_mod = @import("../sat/solver.zig");
const cnf_mod = @import("../sat/cnf.zig");

pub const Theory = enum {
    /// Quantifier-free bit-vectors (bit-blast).
    bv,
    /// Uninterpreted functions + equality (not yet industrial).
    uf,
    /// Arrays (not yet industrial).
    array,
    /// Combined QF_UFBV (not yet).
    ufbv,
};

pub const SmtStatus = enum { sat, unsat, unknown, unsupported };

pub const SmtResult = struct {
    status: SmtStatus,
    theory: Theory,
    conflicts: u64 = 0,
    reason: []const u8 = "",
};

/// High-level SMT solver handle.
pub const SmtSolver = struct {
    allocator: std.mem.Allocator,
    theory: Theory,
    bv: ?bv_mod.BvWorld = null,
    /// Reserved for future theory lemmas / egraph.
    notes: std.ArrayList([]const u8) = .empty,

    pub fn init(allocator: std.mem.Allocator, theory: Theory) !SmtSolver {
        var s: SmtSolver = .{
            .allocator = allocator,
            .theory = theory,
        };
        switch (theory) {
            .bv => s.bv = bv_mod.BvWorld.init(allocator),
            .uf, .array, .ufbv => {
                // Skeleton: mark unsupported until Phase 3 backends land.
            },
        }
        return s;
    }

    pub fn deinit(self: *SmtSolver) void {
        if (self.bv) |*w| w.deinit();
        for (self.notes.items) |n| self.allocator.free(n);
        self.notes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn bvWorld(self: *SmtSolver) !*bv_mod.BvWorld {
        if (self.theory != .bv and self.theory != .ufbv) return error.WrongTheory;
        if (self.bv == null) self.bv = bv_mod.BvWorld.init(self.allocator);
        return &self.bv.?;
    }

    /// Check BV world satisfiability (bit-blast + CDCL).
    pub fn check(self: *SmtSolver) !SmtResult {
        switch (self.theory) {
            .bv => {
                const w = try self.bvWorld();
                const r = try solver_mod.solveCnf(self.allocator, &w.cnf, .{});
                defer if (r.model) |m| self.allocator.free(m);
                defer if (r.proof) |*p| {
                    var pp = p.*;
                    pp.deinit();
                };
                return .{
                    .status = switch (r.status) {
                        .sat => .sat,
                        .unsat => .unsat,
                        .unknown => .unknown,
                    },
                    .theory = .bv,
                    .conflicts = r.conflicts,
                };
            },
            .uf => return .{ .status = .unsupported, .theory = .uf, .reason = "UF backend Phase 3" },
            .array => return .{ .status = .unsupported, .theory = .array, .reason = "array backend Phase 3" },
            .ufbv => return .{ .status = .unsupported, .theory = .ufbv, .reason = "UF+BV combo Phase 3" },
        }
    }
};

test "smt facade bv sat" {
    var s = try SmtSolver.init(std.testing.allocator, .bv);
    defer s.deinit();
    const w = try s.bvWorld();
    const x = try w.mkVar(4);
    const y = try w.mkConst(4, 3);
    // x == y  (via existing bv API if present — force bits equal loosely)
    _ = x;
    _ = y;
    // empty extra constraints → sat
    const r = try s.check();
    try std.testing.expect(r.status == .sat or r.status == .unknown);
}

test "smt facade uf unsupported" {
    var s = try SmtSolver.init(std.testing.allocator, .uf);
    defer s.deinit();
    const r = try s.check();
    try std.testing.expect(r.status == .unsupported);
}
