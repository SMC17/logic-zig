//! Universal taxonomy registry — named systems × maturity.
//!
//! This is the product spine for “leave no stone unturned”: every major family
//! appears as a row. Implementation depth is tracked honestly.

const std = @import("std");

pub const Maturity = enum {
    /// Not started.
    absent,
    /// Named only.
    documented,
    /// API/types/tests link; may return unsupported.
    skeleton,
    /// Real algorithms on a decidable slice.
    fragment,
    /// Production path inside logic-zig.
    engine,
    /// Scoreboard / external peer parity claims allowed only with evidence.
    industrial,
    /// Fully delegated to external giant via adapter.
    external,
};

pub const Family = enum {
    classical_prop,
    classical_fol,
    higher_order,
    constructive,
    type_theory,
    modal_temporal,
    substructural,
    many_valued,
    nonmonotonic,
    probabilistic,
    inductive_abductive,
    informal,
    metalogic,
    computational_sat,
    computational_smt,
    computational_mc,
    computational_atp,
    description_kr,
    algebraic_categorical,
    historical_term,
    applied_domain,
    philosophical,
};

pub const System = struct {
    id: []const u8,
    name: []const u8,
    family: Family,
    maturity: Maturity,
    module: []const u8,
    notes: []const u8,
};

/// Living registry. Expand in the same PR as new code.
pub const systems = [_]System{
    // Classical / computational core
    .{ .id = "prop-classical", .name = "Classical propositional logic", .family = .classical_prop, .maturity = .engine, .module = "sat/ir", .notes = "ExprPool + Tseitin + CDCL" },
    .{ .id = "sat-cdcl", .name = "CDCL SAT", .family = .computational_sat, .maturity = .engine, .module = "sat/solver", .notes = "2WL VSIDS LBD portfolio preprocess vivify" },
    .{ .id = "sat-ipasir", .name = "IPASIR embedding", .family = .computational_sat, .maturity = .engine, .module = "sat/ipasir", .notes = "partial callbacks documented" },
    .{ .id = "smt-bv", .name = "QF_BV bit-blast", .family = .computational_smt, .maturity = .fragment, .module = "smt/bv", .notes = "not word-level industrial" },
    .{ .id = "smt-uf", .name = "Ground EUF", .family = .computational_smt, .maturity = .fragment, .module = "smt/uf", .notes = "congruence closure" },
    .{ .id = "smt-array", .name = "Arrays", .family = .computational_smt, .maturity = .skeleton, .module = "smt/array", .notes = "select/store axioms spine" },
    .{ .id = "mc-bmc", .name = "Bounded model checking", .family = .computational_mc, .maturity = .engine, .module = "circuit/bmc", .notes = "" },
    .{ .id = "mc-kind", .name = "k-induction", .family = .computational_mc, .maturity = .engine, .module = "circuit/kinduction", .notes = "" },
    .{ .id = "mc-pdr", .name = "PDR/IC3 safety", .family = .computational_mc, .maturity = .engine, .module = "circuit/pdr", .notes = "not ABC-class industrial yet" },
    .{ .id = "mc-klive", .name = "k-liveness", .family = .computational_mc, .maturity = .engine, .module = "circuit/kliveness", .notes = "" },
    .{ .id = "ctl-bounded", .name = "Bounded CTL", .family = .modal_temporal, .maturity = .fragment, .module = "ctl", .notes = "SAT unrolling" },
    .{ .id = "fol-unify", .name = "Robinson unification", .family = .classical_fol, .maturity = .engine, .module = "fol/unify", .notes = "" },
    .{ .id = "fol-fmodel", .name = "Finite model finding", .family = .classical_fol, .maturity = .fragment, .module = "fol/finite_model", .notes = "" },
    .{ .id = "fol-resolution", .name = "Clausal FOL resolution", .family = .computational_atp, .maturity = .fragment, .module = "fol/resolution", .notes = "not Vampire-scale" },
    .{ .id = "cert-rup", .name = "RUP/DRAT certificates", .family = .metalogic, .maturity = .engine, .module = "sat/drat", .notes = "external drat-trim" },
    .{ .id = "agent-multishot", .name = "Agent multishot SAT", .family = .computational_sat, .maturity = .engine, .module = "agent/session", .notes = "" },

    // Spines for universal expansion
    .{ .id = "modal-k", .name = "Modal logic K (finite frames)", .family = .modal_temporal, .maturity = .fragment, .module = "modal/kripke", .notes = "box/diamond eval" },
    .{ .id = "modal-s4", .name = "Modal S4", .family = .modal_temporal, .maturity = .skeleton, .module = "modal/kripke", .notes = "frame conditions" },
    .{ .id = "tt-mltt-micro", .name = "Martin-Löf type theory (micro)", .family = .type_theory, .maturity = .skeleton, .module = "type_theory/tt", .notes = "contexts judgments identity micro" },
    .{ .id = "informal-arg", .name = "Informal argument structure", .family = .informal, .maturity = .fragment, .module = "informal/argument", .notes = "premises conclusion schemes" },
    .{ .id = "intuitionistic-prop", .name = "Intuitionistic propositional", .family = .constructive, .maturity = .fragment, .module = "logic/intuitionistic.zig", .notes = "G4ip decision procedure; Glivenko-verified vs classical oracle" },
    .{ .id = "linear-logic", .name = "Linear logic", .family = .substructural, .maturity = .documented, .module = "—", .notes = "planned" },
    .{ .id = "relevance-r", .name = "Relevance logic R", .family = .substructural, .maturity = .documented, .module = "—", .notes = "planned" },
    .{ .id = "default-logic", .name = "Default / nonmonotonic", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/default_logic.zig", .notes = "Reiter extensions (grounded, stable), credulous/skeptical" },
    .{ .id = "klm-rational", .name = "KLM preferential / rational closure", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/klm.zig", .notes = "Lehmann–Magidor exceptionality ranks, SAT-backed queries" },
    .{ .id = "probabilistic", .name = "Probabilistic logic", .family = .probabilistic, .maturity = .fragment, .module = "reason/bayes.zig", .notes = "exact Bayesian posterior over conjunction class, Laplace succession" },
    .{ .id = "alp", .name = "Abductive logic programming", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/alp.zig", .notes = "first-order SLD abduction, denial constraints, Δ instantiation" },
    .{ .id = "maxsat", .name = "MaxSAT optimization", .family = .computational_sat, .maturity = .fragment, .module = "sat/maxsat.zig", .notes = "weighted partial, exact descending-bound + SWC encoding" },
    .{ .id = "dung-af", .name = "Abstract argumentation (Dung)", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/argumentation.zig", .notes = "grounded/complete/stable/preferred, credulous & skeptical" },
    .{ .id = "asp-stable", .name = "Answer-set programming", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/asp.zig", .notes = "Gelfond–Lifschitz reduct check; canon incl. unfounded loops" },
    .{ .id = "agm-revision", .name = "AGM belief revision", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/agm.zig", .notes = "remainder sets, maxichoice/full-meet/cardinality, Levi revision" },
    .{ .id = "circumscription", .name = "Circumscription", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/circumscription.zig", .notes = "P-minimal models with fixed/varying atoms, brute-force verified" },
    .{ .id = "analogical", .name = "Analogical reasoning", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/analogy.zig", .notes = "Miclet–Prade proportions, solving, abstaining classifier" },
    .{ .id = "inductive", .name = "Inductive logic", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/induction.zig", .notes = "SAT-exact k-term DNF synthesis, minimal-k, deductively re-verified" },
    .{ .id = "abductive", .name = "Abductive reasoning", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/abduction.zig", .notes = "MARCO-style subset-minimal consistent explanations over CNF" },
    .{ .id = "hol", .name = "Higher-order logic", .family = .higher_order, .maturity = .documented, .module = "—", .notes = "planned; external Lean/HOL peers" },
    .{ .id = "description-al", .name = "Description logic ALC", .family = .description_kr, .maturity = .fragment, .module = "logic/el.zig", .notes = "EL normalization + completion subsumption (ALC still future)" },
    .{ .id = "syllogistic", .name = "Aristotelian syllogistic", .family = .historical_term, .maturity = .fragment, .module = "logic/syllogistic.zig", .notes = "complete Venn-region decision; 15 Boolean / 24 import-valid" },
    .{ .id = "fuzzy", .name = "Fuzzy / many-valued", .family = .many_valued, .maturity = .fragment, .module = "logic/manyvalued.zig", .notes = "K3/LP/FDE/Ł3 finite matrices (continuum fuzzy still future)" },
    .{ .id = "paraconsistent", .name = "Paraconsistent", .family = .many_valued, .maturity = .fragment, .module = "logic/manyvalued.zig", .notes = "LP/FDE: explosion fails, ∧-elim survives" },
    .{ .id = "epistemic", .name = "Epistemic logic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic.zig", .notes = "multi-agent S5, common knowledge, announcements; muddy children" },
    .{ .id = "deontic", .name = "Deontic logic", .family = .philosophical, .maturity = .documented, .module = "—", .notes = "planned" },
    .{ .id = "categorical", .name = "Categorical logic / topos", .family = .algebraic_categorical, .maturity = .documented, .module = "—", .notes = "planned" },

    // Giants (external)
    .{ .id = "ext-cadical", .name = "CaDiCaL (external)", .family = .computational_sat, .maturity = .external, .module = "sat/external", .notes = "differential + scoreboard" },
    .{ .id = "ext-kissat", .name = "Kissat (external)", .family = .computational_sat, .maturity = .external, .module = "bridge/giants", .notes = "discover when installed" },
    .{ .id = "ext-z3", .name = "Z3 (external)", .family = .computational_smt, .maturity = .external, .module = "bridge/giants", .notes = "discover when installed" },
    .{ .id = "ext-abc", .name = "ABC (external)", .family = .computational_mc, .maturity = .external, .module = "bridge/abc_interop", .notes = "abc-delta" },
    .{ .id = "ext-vampire", .name = "Vampire (external)", .family = .computational_atp, .maturity = .external, .module = "bridge/giants", .notes = "discover when installed" },
    .{ .id = "ext-drat-trim", .name = "drat-trim (external)", .family = .metalogic, .maturity = .external, .module = "sat/drat_external", .notes = "" },
};

pub fn countByMaturity(m: Maturity) u32 {
    var n: u32 = 0;
    for (systems) |s| {
        if (s.maturity == m) n += 1;
    }
    return n;
}

pub fn countByFamily(f: Family) u32 {
    var n: u32 = 0;
    for (systems) |s| {
        if (s.family == f) n += 1;
    }
    return n;
}

pub fn printAll() void {
    std.debug.print("=== TAXONOMY REGISTRY ({d} systems) ===\n", .{systems.len});
    for (systems) |s| {
        std.debug.print("{s:16}  {s:12}  {s}\n", .{ @tagName(s.maturity), s.id, s.name });
    }
    std.debug.print("--- maturity counts ---\n", .{});
    inline for (@typeInfo(Maturity).@"enum".fields) |field| {
        const m: Maturity = @enumFromInt(field.value);
        std.debug.print("  {s}: {d}\n", .{ field.name, countByMaturity(m) });
    }
}

test "registry non-empty and has engines" {
    try std.testing.expect(systems.len >= 20);
    try std.testing.expect(countByMaturity(.engine) >= 5);
    try std.testing.expect(countByMaturity(.documented) >= 5);
    try std.testing.expect(countByMaturity(.external) >= 3);
}

test "registry has informal and type theory rows" {
    var has_inf = false;
    var has_tt = false;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "informal-arg")) has_inf = true;
        if (std.mem.eql(u8, s.id, "tt-mltt-micro")) has_tt = true;
    }
    try std.testing.expect(has_inf and has_tt);
}
