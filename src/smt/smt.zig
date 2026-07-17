//! SMT facade — industrial SMT program (Phase 3).
//!
//! - **BV**: bit-blast (`bv.zig`)
//! - **UF**: ground EUF congruence closure (`uf.zig`)
//! - **array / ufbv**: unsupported until backends land

const std = @import("std");
const bv_mod = @import("bv.zig");
const uf_mod = @import("uf.zig");
const solver_mod = @import("../sat/solver.zig");

pub const Theory = enum {
    bv,
    uf,
    array,
    ufbv,
};

pub const SmtStatus = enum { sat, unsat, unknown, unsupported };

pub const SmtResult = struct {
    status: SmtStatus,
    theory: Theory,
    conflicts: u64 = 0,
    reason: []const u8 = "",
};

pub const SmtSolver = struct {
    allocator: std.mem.Allocator,
    theory: Theory,
    bv: ?bv_mod.BvWorld = null,
    uf: ?uf_mod.UfSolver = null,
    notes: std.ArrayList([]const u8) = .empty,

    pub fn init(allocator: std.mem.Allocator, theory: Theory) !SmtSolver {
        var s: SmtSolver = .{
            .allocator = allocator,
            .theory = theory,
        };
        switch (theory) {
            .bv => s.bv = bv_mod.BvWorld.init(allocator),
            .uf => s.uf = uf_mod.UfSolver.init(allocator),
            .array, .ufbv => {},
        }
        return s;
    }

    pub fn deinit(self: *SmtSolver) void {
        if (self.bv) |*w| w.deinit();
        if (self.uf) |*w| w.deinit();
        for (self.notes.items) |n| self.allocator.free(n);
        self.notes.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn bvWorld(self: *SmtSolver) !*bv_mod.BvWorld {
        if (self.theory != .bv and self.theory != .ufbv) return error.WrongTheory;
        if (self.bv == null) self.bv = bv_mod.BvWorld.init(self.allocator);
        return &self.bv.?;
    }

    pub fn ufSolver(self: *SmtSolver) !*uf_mod.UfSolver {
        if (self.theory != .uf and self.theory != .ufbv) return error.WrongTheory;
        if (self.uf == null) self.uf = uf_mod.UfSolver.init(self.allocator);
        return &self.uf.?;
    }

    pub fn check(self: *SmtSolver) !SmtResult {
        switch (self.theory) {
            .bv => {
                const w = try self.bvWorld();
                const r = try solver_mod.solveCnf(self.allocator, &w.cnf, .{
                    .preprocess = true,
                    .inprocess_interval = 2000,
                    .pure_literal = true,
                });
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
            .uf => {
                const u = try self.ufSolver();
                return .{
                    .status = if (u.check() == .sat) .sat else .unsat,
                    .theory = .uf,
                };
            },
            .array => return .{ .status = .unsupported, .theory = .array, .reason = "array backend later" },
            .ufbv => return .{ .status = .unsupported, .theory = .ufbv, .reason = "UF+BV combo later" },
        }
    }
};

test "smt facade bv sat" {
    var s = try SmtSolver.init(std.testing.allocator, .bv);
    defer s.deinit();
    _ = try s.bvWorld();
    const r = try s.check();
    try std.testing.expect(r.status == .sat or r.status == .unknown);
}

test "smt facade uf works" {
    var s = try SmtSolver.init(std.testing.allocator, .uf);
    defer s.deinit();
    const u = try s.ufSolver();
    const a = try u.mkConst("a");
    const b = try u.mkConst("b");
    u.assertEq(a, b);
    try u.assertDiseq(a, b);
    const r = try s.check();
    try std.testing.expect(r.status == .unsat);
}
