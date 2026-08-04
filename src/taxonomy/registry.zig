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
    .{ .id = "natded", .name = "Natural deduction (Fitch)", .family = .classical_prop, .maturity = .fragment, .module = "deductive/natded", .notes = "assume →I/E ∧I/E ¬E ⊥E; checked proof object" },
    .{ .id = "sequent-lk", .name = "Sequent calculus LK", .family = .classical_prop, .maturity = .fragment, .module = "deductive/sequent", .notes = "Γ ⊢ Δ rules + checked proof nodes" },
    .{ .id = "sequent-search", .name = "Automated sequent search", .family = .classical_prop, .maturity = .fragment, .module = "deductive/sequent_search", .notes = "backward-chaining invertible rules, depth-bounded" },
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
    .{ .id = "intuitionistic-prop", .name = "Intuitionistic propositional", .family = .constructive, .maturity = .fragment, .module = "constructive/intuitionistic", .notes = "finite Kripke; LEM countermodel" },
    .{ .id = "linear-logic", .name = "Linear logic ILL", .family = .substructural, .maturity = .fragment, .module = "substructural/linear", .notes = "⊗ ⊸ & ⊕ ! + resource bags" },
    .{ .id = "relevance-r", .name = "Relevance logic R", .family = .substructural, .maturity = .documented, .module = "—", .notes = "planned" },
    .{ .id = "default-logic", .name = "Default / nonmonotonic", .family = .nonmonotonic, .maturity = .fragment, .module = "nonmonotonic/default", .notes = "Reiter extensions ≤12 defaults" },
    .{ .id = "probabilistic", .name = "Probabilistic logic", .family = .probabilistic, .maturity = .fragment, .module = "probabilistic/prob", .notes = "independence eval + Fréchet bounds" },
    .{ .id = "inductive", .name = "Inductive logic", .family = .inductive_abductive, .maturity = .fragment, .module = "inductive/induction", .notes = "schema + Peano/list datatypes; k-induction remains in circuit/" },
    .{ .id = "abductive", .name = "Abductive reasoning", .family = .inductive_abductive, .maturity = .fragment, .module = "abductive/abduce", .notes = "propositional minimal explanations via CDCL; ≤16 abducibles" },
    .{ .id = "abductive-industrial", .name = "Industrial abduction", .family = .inductive_abductive, .maturity = .fragment, .module = "abductive/industrial", .notes = "greedy hitting-set + prune; scales past 2^n" },
    .{ .id = "hol", .name = "Higher-order logic", .family = .higher_order, .maturity = .documented, .module = "—", .notes = "planned; external Lean/HOL peers" },
    .{ .id = "description-al", .name = "Description logic ALC", .family = .description_kr, .maturity = .fragment, .module = "description/alc", .notes = "concepts + ∧-expansion tableau clash" },
    .{ .id = "syllogistic", .name = "Aristotelian syllogistic", .family = .historical_term, .maturity = .fragment, .module = "historical/syllogistic", .notes = "24 valid moods × 4 figures" },
    .{ .id = "fuzzy", .name = "Fuzzy / many-valued", .family = .many_valued, .maturity = .fragment, .module = "fuzzy/fuzzy", .notes = "Gödel/product/Łukasiewicz t-norms + Kleene 3-valued" },
    .{ .id = "paraconsistent", .name = "Paraconsistent LP", .family = .many_valued, .maturity = .fragment, .module = "paraconsistent/lp", .notes = "Belnap-Dunn four-valued; explosion fails" },
    .{ .id = "epistemic", .name = "Epistemic logic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic_deontic", .notes = "multi-agent K_i on Kripke" },
    .{ .id = "deontic", .name = "Deontic logic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic_deontic", .notes = "O/P + serial frame check" },
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

test "registry has inductive abductive fuzzy fragments" {
    var has_ind = false;
    var has_abd = false;
    var has_fuz = false;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "inductive") and s.maturity == .fragment) has_ind = true;
        if (std.mem.eql(u8, s.id, "abductive") and s.maturity == .fragment) has_abd = true;
        if (std.mem.eql(u8, s.id, "fuzzy") and s.maturity == .fragment) has_fuz = true;
    }
    try std.testing.expect(has_ind and has_abd and has_fuz);
}

test "registry has natded fragment" {
    var has = false;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "natded") and s.maturity == .fragment) has = true;
    }
    try std.testing.expect(has);
}

test "registry v0.19 fragments" {
    var n: u32 = 0;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "sequent-lk") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "paraconsistent") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "syllogistic") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "default-logic") and s.maturity == .fragment) n += 1;
    }
    try std.testing.expect(n == 4);
}

test "registry v0.20 fragments" {
    var n: u32 = 0;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "intuitionistic-prop") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "linear-logic") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "probabilistic") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "description-al") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "epistemic") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "deontic") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "sequent-search") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "abductive-industrial") and s.maturity == .fragment) n += 1;
    }
    try std.testing.expect(n == 8);
}
