//! Stable public API (v1) — the contract for external consumers and spin-offs.
//!
//! Semver for this surface: **1.x**. Breaking changes require `api/v2`.
//! Internal modules (`sat/solver.zig`, …) may move; prefer calling through here
//! for long-lived integrations.
//!
//! See `docs/INDUSTRIAL.md` for the full industrial program.

const std = @import("std");
const solver_mod = @import("../sat/solver.zig");
const cnf_mod = @import("../sat/cnf.zig");
const portfolio_mod = @import("../sat/portfolio.zig");
const preprocess_mod = @import("../sat/preprocess.zig");
const dimacs = @import("../bridge/dimacs.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const kinduction = @import("../circuit/kinduction.zig");
const netlist_mod = @import("../circuit/netlist.zig");
const aiger = @import("../bridge/aiger.zig");
const bv_mod = @import("../smt/bv.zig");
const smt_mod = @import("../smt/smt.zig");
const ctl_mod = @import("../ctl/ctl.zig");
const resolution = @import("../fol/resolution.zig");
const certificate = @import("../cert/certificate.zig");
const agent_session = @import("../agent/session.zig");

/// API major.minor — bump minor for additive; major requires new module path.
pub const version_major: u32 = 1;
pub const version_minor: u32 = 0;
pub const version_string = "1.0.0";

/// Feature bits — consumers can feature-detect without parsing docs.
pub const Capability = packed struct(u32) {
    sat_cdcl: bool = true,
    sat_portfolio: bool = true,
    sat_preprocess: bool = true,
    sat_proof_rup: bool = true,
    sat_ipasir: bool = true,
    mc_bmc: bool = true,
    mc_kind: bool = true,
    mc_pdr: bool = true,
    mc_justice: bool = true,
    mc_klive: bool = true,
    cert_pdr: bool = true,
    agent_session: bool = true,
    smt_bv: bool = true,
    smt_uf: bool = true, // ground EUF spine
    smt_array: bool = true, // partial read-over-write only (not full array theory)
    fol_unify: bool = true,
    fol_finite_model: bool = true,
    fol_resolution: bool = true, // Phase 4 skeleton
    ctl_bounded: bool = true,
    abc_interop: bool = true,
    _pad: u12 = 0,

    pub fn current() Capability {
        return .{};
    }

    pub fn toU32(self: Capability) u32 {
        return @bitCast(self);
    }
};

pub fn versionLine(allocator: std.mem.Allocator) ![]u8 {
    return std.fmt.allocPrint(allocator, "logic-zig api/v1 {s} caps=0x{x}", .{
        version_string,
        Capability.current().toU32(),
    });
}

// ── SAT ──────────────────────────────────────────────────────────────

pub const SatOptions = struct {
    max_conflicts: u64 = std.math.maxInt(u64),
    proof: bool = false,
    portfolio: bool = false,
    portfolio_budget: u64 = 2_000_000,
    /// Run cheap CNF preprocess (subsumption / tautology drop).
    preprocess: bool = true,
};

pub const SatResult = solver_mod.SolveResult;

pub fn satCnf(
    allocator: std.mem.Allocator,
    formula: *cnf_mod.Cnf,
    opts: SatOptions,
) !SatResult {
    if (opts.preprocess) {
        _ = try preprocess_mod.preprocess(allocator, formula);
    }
    if (opts.portfolio) {
        const pr = try portfolio_mod.solvePortfolioOpts(allocator, formula, .{
            .total_conflicts = opts.portfolio_budget,
            .proof_on_unsat = opts.proof,
            .validate_model = true,
        });
        // Map portfolio Result → SolveResult
        return .{
            .status = pr.status,
            .model = pr.model,
            .conflicts = pr.conflicts,
            .learned = pr.learned,
            .proof = pr.proof,
        };
    }
    return solver_mod.solveCnf(allocator, formula, .{
        .max_conflicts = opts.max_conflicts,
        .proof = opts.proof,
        .complete_model = true,
        .preprocess = false, // already applied above when opts.preprocess
        .inprocess_interval = 2000,
        .pure_literal = true,
    });
}

pub fn satDimacs(
    allocator: std.mem.Allocator,
    src: []const u8,
    opts: SatOptions,
) !SatResult {
    var cnf = try dimacs.parse(allocator, src);
    defer cnf.deinit();
    // Ownership: model/proof allocated; cnf destroyed — need owned solve on copy.
    // solveCnf clones clause DB into solver, so OK.
    return satCnf(allocator, &cnf, opts);
}

// ── MC ───────────────────────────────────────────────────────────────

pub const McEngine = enum { auto, pdr, kind, bmc };

pub const McOptions = struct {
    max_frames: u32 = 16,
    engine: McEngine = .auto,
    cert: bool = false,
};

pub const McStatus = enum { proven, violated, unknown };

pub const McResult = struct {
    status: McStatus,
    engine: []const u8 = "",
    frames: u32 = 0,
    cert_verified: bool = false,
};

pub fn mcSafety(
    allocator: std.mem.Allocator,
    nl: *netlist_mod.Netlist,
    bad: netlist_mod.NetId,
    opts: McOptions,
) !McResult {
    const eng = opts.engine;
    if (eng == .auto or eng == .pdr) {
        var pr = try pdr.check(allocator, nl, bad, opts.max_frames);
        defer pr.deinit(allocator);
        switch (pr.status) {
            .proven => {
                var cert_ok = false;
                if (opts.cert) {
                    if (try certificate.fromPdrProven(allocator, nl, bad, opts.max_frames)) |*inv| {
                        defer {
                            var ii = inv.*;
                            ii.deinit();
                        }
                        cert_ok = try inv.verify(allocator, nl);
                    }
                }
                return .{ .status = .proven, .engine = "pdr", .frames = pr.frames, .cert_verified = cert_ok };
            },
            .violated => return .{ .status = .violated, .engine = "pdr", .frames = pr.frames },
            .unknown => if (eng == .pdr) return .{ .status = .unknown, .engine = "pdr", .frames = pr.frames },
        }
    }
    if (eng == .auto or eng == .kind) {
        const kr = try kinduction.search(allocator, nl, bad, @min(opts.max_frames, 8));
        defer if (kr.base.trace) |t| allocator.free(t);
        switch (kr.status) {
            .proven => return .{ .status = .proven, .engine = "kind", .frames = kr.k },
            .violated => return .{ .status = .violated, .engine = "kind", .frames = kr.k },
            .base_only, .unknown => if (eng == .kind) return .{ .status = .unknown, .engine = "kind", .frames = kr.k },
        }
    }
    // BMC last
    const br = try bmc.check(allocator, nl, bad, opts.max_frames);
    defer if (br.trace) |t| allocator.free(t);
    return switch (br.status) {
        .violated => .{ .status = .violated, .engine = "bmc", .frames = br.bound },
        .safe_up_to_bound => .{ .status = .unknown, .engine = "bmc", .frames = br.bound },
        .unknown => .{ .status = .unknown, .engine = "bmc", .frames = br.bound },
    };
}

/// Multi-property safety: OR of all bads (HWMCC combined semantics).
/// Empty props → proven (vacuous).
pub fn mcSafetyMulti(
    allocator: std.mem.Allocator,
    nl: *netlist_mod.Netlist,
    bads: []const netlist_mod.NetId,
    opts: McOptions,
) !McResult {
    if (bads.len == 0) return .{ .status = .proven, .engine = "empty", .frames = 0 };
    if (bads.len == 1) return mcSafety(allocator, nl, bads[0], opts);

    const eng = opts.engine;
    if (eng == .auto or eng == .pdr) {
        var pr = try pdr.checkMulti(allocator, nl, bads, opts.max_frames);
        defer pr.deinit(allocator);
        switch (pr.status) {
            .proven => return .{ .status = .proven, .engine = "pdr-multi", .frames = pr.frames },
            .violated => return .{ .status = .violated, .engine = "pdr-multi", .frames = pr.frames },
            .unknown => if (eng == .pdr) return .{ .status = .unknown, .engine = "pdr-multi", .frames = pr.frames },
        }
    }
    // k-induction on OR-synthesized property is awkward; BMC multi first for CEX.
    if (eng == .auto or eng == .bmc or eng == .kind) {
        const br = try bmc.checkMulti(allocator, nl, bads, opts.max_frames);
        defer if (br.trace) |t| allocator.free(t);
        switch (br.status) {
            .violated => return .{ .status = .violated, .engine = "bmc-multi", .frames = br.bound },
            .safe_up_to_bound => {
                if (eng == .bmc) return .{ .status = .unknown, .engine = "bmc-multi", .frames = br.bound };
                // auto/kind: still unknown at bound (no multi-kind yet)
                return .{ .status = .unknown, .engine = "bmc-multi", .frames = br.bound };
            },
            .unknown => return .{ .status = .unknown, .engine = "bmc-multi", .frames = br.bound },
        }
    }
    return .{ .status = .unknown, .engine = "multi", .frames = 0 };
}

pub fn mcAiger(
    allocator: std.mem.Allocator,
    src: []const u8,
    opts: McOptions,
) !McResult {
    var nl = try aiger.parse(allocator, src);
    defer nl.deinit();
    const props = nl.badProps();
    return mcSafetyMulti(allocator, &nl, props, opts);
}

// ── SMT / CTL / FOL / Agent re-exports ───────────────────────────────

pub const BvWorld = bv_mod.BvWorld;
pub const SmtSolver = smt_mod.SmtSolver;
pub const SmtTheory = smt_mod.Theory;
pub const UfSolver = @import("../smt/uf.zig").UfSolver;
pub const ArraySolver = @import("../smt/array.zig").ArraySolver;
pub const CtlOp = ctl_mod.CtlOp;
pub const checkCtl = ctl_mod.check;
pub const FolResolution = resolution.Prover;
pub const Session = agent_session.Session;

test "api v1 version and caps" {
    const line = try versionLine(std.testing.allocator);
    defer std.testing.allocator.free(line);
    try std.testing.expect(std.mem.indexOf(u8, line, "1.0.0") != null);
    const caps = Capability.current();
    try std.testing.expect(caps.sat_cdcl);
    try std.testing.expect(caps.fol_resolution);
    try std.testing.expect(caps.smt_uf);
}

test "api v1 sat unsat" {
    const src =
        \\p cnf 1 2
        \\1 0
        \\-1 0
    ;
    var r = try satDimacs(std.testing.allocator, src, .{ .preprocess = true });
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .unsat);
}

test "api v1 sat sat" {
    const src =
        \\p cnf 2 1
        \\1 2 0
    ;
    var r = try satDimacs(std.testing.allocator, src, .{});
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .sat);
}

test "api v1 mcAiger empty bad proven" {
    const src =
        \\aag 1 0 1 0 0
        \\0 0
    ;
    const r = try mcAiger(std.testing.allocator, src, .{ .max_frames = 4 });
    try std.testing.expect(r.status == .proven);
    try std.testing.expectEqualStrings("empty", r.engine);
}

test "api v1 mcAiger multi-bad violated" {
    // q0 stuck0 + q1 init1 stuck1; combined OR unsafe
    const src =
        \\aag 2 0 2 0 0 2 0 0 0
        \\0 0
        \\1 1
        \\2
        \\4
    ;
    const r = try mcAiger(std.testing.allocator, src, .{ .max_frames = 8 });
    try std.testing.expect(r.status == .violated);
}

test "api v1 mcAiger stuck0 proven" {
    const src =
        \\aag 1 0 1 1 0
        \\0 0
        \\2
    ;
    const r = try mcAiger(std.testing.allocator, src, .{ .max_frames = 12 });
    try std.testing.expect(r.status == .proven or r.status == .unknown);
    try std.testing.expect(r.status != .violated);
}
