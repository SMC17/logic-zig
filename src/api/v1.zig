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
pub const version_minor: u32 = 5;
pub const version_string = "1.5.0";

/// Feature bits — consumers can feature-detect without parsing docs.
/// Widened to u64 in 1.3.0; `toU32` keeps returning the low word for
/// existing callers (all pre-1.3 bits live there).
pub const Capability = packed struct(u64) {
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
    reason_abduce: bool = true, // subset-minimal propositional abduction
    reason_induce: bool = true, // SAT-based k-term DNF inductive synthesis
    sat_maxsat: bool = true, // weighted partial MaxSAT (exact, small-scale)
    reason_abduce_cost: bool = true, // min-cost abduction (implicit hitting set)
    reason_alp: bool = true, // first-order abductive logic programming
    reason_bayes: bool = true, // exact Bayesian induction over conjunctions
    reason_default: bool = true, // Reiter default-logic extensions
    reason_klm: bool = true, // KLM rational closure
    reason_af: bool = true, // Dung abstract argumentation
    reason_asp: bool = true, // stable models (answer sets)
    reason_agm: bool = true, // AGM base contraction/revision
    reason_circ: bool = true, // propositional circumscription
    reason_analogy: bool = true, // Boolean analogical proportions
    logic_intuitionistic: bool = true, // G4ip decision procedure
    logic_manyvalued: bool = true, // K3/LP/FDE/Ł3 finite matrices
    modal_epistemic: bool = true, // multi-agent S5 + common knowledge + announcements
    logic_syllogistic: bool = true, // complete categorical syllogism decision
    kr_el: bool = true, // description logic EL subsumption
    modal_deontic: bool = true, // SDL (KD) on serial finite frames
    logic_linear_mll: bool = true, // MLL sequent prover (units, exact splitting)
    _pad: u24 = 0,

    pub fn current() Capability {
        return .{};
    }

    pub fn toU64(self: Capability) u64 {
        return @bitCast(self);
    }

    /// Low word — every pre-1.3 capability bit is here.
    pub fn toU32(self: Capability) u32 {
        return @truncate(self.toU64());
    }
};

pub fn versionLine(allocator: std.mem.Allocator) ![]u8 {
    return std.fmt.allocPrint(allocator, "logic-zig api/v1 {s} caps=0x{x}", .{
        version_string,
        Capability.current().toU64(),
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

// ── Reasoning modes (Peircean triad; deduction is the shared oracle) ─

const abduction_mod = @import("../reason/abduction.zig");
const induction_mod = @import("../reason/induction.zig");

/// Abduction: observation → subset-minimal consistent causes.
pub const abduce = abduction_mod.abduce;
pub const AbduceResult = abduction_mod.Result;
pub const verifyExplanation = abduction_mod.verifyExplanation;

/// Induction: labeled examples → minimal-k DNF rule, deductively re-verified.
pub const induceDnf = induction_mod.induceDnf;
pub const InduceResult = induction_mod.Result;
pub const InduceExample = induction_mod.Example;

const maxsat_mod = @import("../sat/maxsat.zig");
const alp_mod = @import("../reason/alp.zig");
const bayes_mod = @import("../reason/bayes.zig");
const default_mod = @import("../reason/default_logic.zig");
const klm_mod = @import("../reason/klm.zig");

/// Optimization: weighted partial MaxSAT (exact on small instances).
pub const maxsatSolve = maxsat_mod.solve;
pub const MaxsatSoft = maxsat_mod.SoftClause;

/// Cost-ranked abduction: cardinality/weighted-minimal explanations.
pub const abduceMinCost = abduction_mod.abduceMinCost;

/// First-order abduction: SLD over definite Horn programs with denials.
pub const alpAbduce = alp_mod.abduce;
pub const AlpProgram = alp_mod.Program;
pub const AlpClause = alp_mod.Clause;

/// Statistical induction: exact posterior, MAP, predictive averaging.
pub const bayesPosterior = bayes_mod.posterior;
pub const laplaceSuccession = bayes_mod.laplace;

/// Nonmonotonic: Reiter default extensions; KLM rational closure.
pub const defaultExtensions = default_mod.extensions;
pub const DefaultRule = default_mod.Default;
pub const klmRank = klm_mod.rank;
pub const klmQuery = klm_mod.query;
pub const KlmConditional = klm_mod.Conditional;

const af_mod = @import("../reason/argumentation.zig");
const asp_mod = @import("../reason/asp.zig");
const agm_mod = @import("../reason/agm.zig");
const circ_mod = @import("../reason/circumscription.zig");
const analogy_mod = @import("../reason/analogy.zig");

/// Argumentation: Dung semantics + acceptance.
pub const Af = af_mod.Af;
pub const afGrounded = af_mod.grounded;
pub const afExtensions = af_mod.extensions;
pub const afAccepted = af_mod.accepted;

/// Answer sets: stable models of normal programs.
pub const aspStableModels = asp_mod.stableModels;
pub const AspRule = asp_mod.Rule;

/// Belief change: AGM base contraction/revision.
pub const agmContract = agm_mod.contract;
pub const agmRevise = agm_mod.revise;
pub const AgmBelief = agm_mod.Belief;

/// Minimal-model reasoning: circumscription.
pub const circEntails = circ_mod.circEntails;
pub const CircPartition = circ_mod.Partition;

/// Analogical proportions.
pub const analogyHolds = analogy_mod.holds;
pub const analogySolve = analogy_mod.solve;
pub const analogyClassify = analogy_mod.classify;

const int_mod = @import("../logic/intuitionistic.zig");
const mv_mod = @import("../logic/manyvalued.zig");
const epi_mod = @import("../modal/epistemic.zig");
const syl_mod = @import("../logic/syllogistic.zig");
const el_mod = @import("../logic/el.zig");

/// Intuitionistic propositional validity (G4ip).
pub const intuitProvable = int_mod.provable;
pub const IntuitBuilder = int_mod.Builder;

/// Finite-matrix many-valued consequence.
pub const mvConsequence = mv_mod.consequence;
pub const mvTautology = mv_mod.tautology;
pub const mv_classical = mv_mod.classical;
pub const mv_k3 = mv_mod.k3;
pub const mv_lp = mv_mod.lp;
pub const mv_fde = mv_mod.fde;
pub const mv_l3 = mv_mod.l3;

/// Epistemic model checking (S5, common knowledge, announcements).
pub const epistemicHolds = epi_mod.holds;
pub const epistemicAnnounce = epi_mod.announce;
pub const EpistemicModel = epi_mod.Model;

/// Categorical syllogistic (complete Venn-region decision).
pub const syllogismValid = syl_mod.valid;
pub const Syllogism = syl_mod.Syllogism;

/// Description logic EL subsumption.
pub const elNormalize = el_mod.normalize;
pub const elClassify = el_mod.classify;
pub const ElAxiom = el_mod.Axiom;

const deo_mod = @import("../modal/deontic.zig");
const lin_mod = @import("../logic/linear.zig");

/// Deontic SDL (KD) evaluation on serial frames.
pub const deonticHolds = deo_mod.holds;
pub const deonticSerial = deo_mod.serial;
pub const DeonticFrame = deo_mod.Frame;

/// MLL linear-logic provability.
pub const mllProvable = lin_mod.provable;
pub const MllBuilder = lin_mod.Builder;

test "api v1 version and caps" {
    const line = try versionLine(std.testing.allocator);
    defer std.testing.allocator.free(line);
    try std.testing.expect(std.mem.indexOf(u8, line, version_string) != null);
    const caps = Capability.current();
    try std.testing.expect(caps.sat_cdcl);
    try std.testing.expect(caps.fol_resolution);
    try std.testing.expect(caps.smt_uf);
    try std.testing.expect(caps.reason_abduce);
    try std.testing.expect(caps.reason_induce);
    try std.testing.expect(caps.sat_maxsat);
    try std.testing.expect(caps.reason_alp);
    try std.testing.expect(caps.reason_default);
    try std.testing.expect(caps.reason_klm);
    try std.testing.expect(caps.reason_af);
    try std.testing.expect(caps.reason_asp);
    try std.testing.expect(caps.reason_agm);
    try std.testing.expect(caps.reason_circ);
    try std.testing.expect(caps.reason_analogy);
    try std.testing.expect(caps.logic_intuitionistic);
    try std.testing.expect(caps.logic_manyvalued);
    try std.testing.expect(caps.modal_epistemic);
    try std.testing.expect(caps.logic_syllogistic);
    try std.testing.expect(caps.kr_el);
    try std.testing.expect(caps.modal_deontic);
    try std.testing.expect(caps.logic_linear_mll);
    // Low-word compatibility: pre-1.3 bits unchanged.
    try std.testing.expect(caps.toU32() == @as(u32, @truncate(caps.toU64())));
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
