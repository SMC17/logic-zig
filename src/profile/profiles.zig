//! Flagship optimization profiles — unique tradeoff packs for spin-offs.
//!
//! Each profile is a named bundle of solver / MC defaults. Spin-off CLIs
//! pin one profile so users get coherent defaults without a 40-flag soup.

const std = @import("std");
const solver_mod = @import("../sat/solver.zig");

pub const ProfileId = enum {
    /// Balanced default (main `logic-zig` CLI).
    core,
    /// Multishot / agent: keep learned clauses, cheap restarts, assume-heavy.
    agent,
    /// SAT-throughput: aggressive reduce, Luby-ish restarts, proof off by default.
    sat_race,
    /// Hardware MC: higher conflict caps for PDR/BMC, proof optional.
    hwmcc,
    /// Certificate-first: proof logging on, conservative reduce.
    cert,
    /// SMT/BV: larger var budgets, complete models.
    smt,
    /// CTL unrolling: tight bounds by default, complete models.
    ctl,
};

pub const Profile = struct {
    id: ProfileId,
    name: []const u8,
    blurb: []const u8,
    solver: solver_mod.SolverOptions,
    /// Default PDR / BMC frame budgets (spin-offs may override).
    max_frames: u32 = 16,
    max_k_liveness: u32 = 8,
    prefer_proof: bool = false,
    multishot_keep_learned: bool = true,
};

pub fn get(id: ProfileId) Profile {
    return switch (id) {
        .core => .{
            .id = .core,
            .name = "core",
            .blurb = "Balanced library defaults",
            .solver = .{},
            .max_frames = 16,
        },
        .agent => .{
            .id = .agent,
            .name = "agent",
            .blurb = "Incremental multishot + assumptions; minimize process overhead",
            .solver = .{
                .max_conflicts = 500_000,
                .restart_base = 80,
                .reduce_interval = 3000,
                .reduce_keep_min = 100,
                .minimize = true,
                .proof = false,
            },
            .max_frames = 8,
            .multishot_keep_learned = true,
        },
        .sat_race => .{
            .id = .sat_race,
            .name = "sat-race",
            .blurb = "Throughput-oriented CDCL (not a competition entry claim)",
            .solver = .{
                .max_conflicts = std.math.maxInt(u64),
                .restart_base = 100,
                .reduce_interval = 1500,
                .reduce_keep_min = 200,
                .reduce_by_lbd = true,
                .minimize = true,
                .proof = false,
            },
            .prefer_proof = false,
        },
        .hwmcc => .{
            .id = .hwmcc,
            .name = "hwmcc",
            .blurb = "Sequential safety/liveness budgets for AIGER-scale nets",
            .solver = .{
                .max_conflicts = 1_000_000,
                .minimize = true,
                .reduce_by_lbd = true,
            },
            .max_frames = 32,
            .max_k_liveness = 12,
        },
        .cert => .{
            .id = .cert,
            .name = "cert",
            .blurb = "Proof-first: RUP on, gentle reduce, export-friendly",
            .solver = .{
                .proof = true,
                .reduce_interval = 5000,
                .minimize = true,
            },
            .prefer_proof = true,
            .max_frames = 24,
        },
        .smt => .{
            .id = .smt,
            .name = "smt",
            .blurb = "Bit-vector bit-blast → CDCL; complete models",
            .solver = .{
                .complete_model = true,
                .max_conflicts = 2_000_000,
            },
        },
        .ctl => .{
            .id = .ctl,
            .name = "ctl",
            .blurb = "Bounded CTL via unrolling; small-state friendly",
            .solver = .{ .complete_model = true, .max_conflicts = 500_000 },
            .max_frames = 12,
        },
    };
}

pub fn list() []const ProfileId {
    return std.enums.values(ProfileId);
}

test "all profiles construct" {
    for (list()) |id| {
        const p = get(id);
        try std.testing.expect(p.name.len > 0);
    }
}
