//! Universal taxonomy registry — named systems × maturity.

const std = @import("std");

pub const Maturity = enum { absent, documented, skeleton, fragment, engine, industrial, external };

pub const Family = enum {
    classical_prop, classical_fol, higher_order, constructive, type_theory,
    modal_temporal, substructural, many_valued, nonmonotonic, probabilistic,
    inductive_abductive, informal, metalogic, computational_sat, computational_smt,
    computational_mc, computational_atp, description_kr, algebraic_categorical,
    historical_term, applied_domain, philosophical,
};

pub const System = struct {
    id: []const u8,
    name: []const u8,
    family: Family,
    maturity: Maturity,
    module: []const u8,
    notes: []const u8,
};

pub const systems = [_]System{
    .{ .id = "prop-classical", .name = "Classical propositional logic", .family = .classical_prop, .maturity = .engine, .module = "sat/ir", .notes = "" },
    .{ .id = "natded", .name = "Natural deduction (Fitch)", .family = .classical_prop, .maturity = .fragment, .module = "deductive/natded", .notes = "" },
    .{ .id = "sequent-lk", .name = "Sequent calculus LK", .family = .classical_prop, .maturity = .fragment, .module = "deductive/sequent", .notes = "" },
    .{ .id = "sequent-search", .name = "Automated sequent search", .family = .classical_prop, .maturity = .fragment, .module = "deductive/sequent_search", .notes = "" },
    .{ .id = "focusing", .name = "Focusing proof search", .family = .classical_prop, .maturity = .fragment, .module = "deductive/focusing", .notes = "" },
    .{ .id = "sat-cdcl", .name = "CDCL SAT", .family = .computational_sat, .maturity = .engine, .module = "sat/solver", .notes = "" },
    .{ .id = "sat-ipasir", .name = "IPASIR embedding", .family = .computational_sat, .maturity = .engine, .module = "sat/ipasir", .notes = "" },
    .{ .id = "smt-bv", .name = "QF_BV bit-blast", .family = .computational_smt, .maturity = .fragment, .module = "smt/bv", .notes = "" },
    .{ .id = "smt-uf", .name = "Ground EUF", .family = .computational_smt, .maturity = .fragment, .module = "smt/uf", .notes = "" },
    .{ .id = "smt-array", .name = "Arrays", .family = .computational_smt, .maturity = .skeleton, .module = "smt/array", .notes = "" },
    .{ .id = "mc-bmc", .name = "Bounded model checking", .family = .computational_mc, .maturity = .engine, .module = "circuit/bmc", .notes = "" },
    .{ .id = "mc-kind", .name = "k-induction", .family = .computational_mc, .maturity = .engine, .module = "circuit/kinduction", .notes = "" },
    .{ .id = "mc-pdr", .name = "PDR/IC3 safety", .family = .computational_mc, .maturity = .engine, .module = "circuit/pdr", .notes = "" },
    .{ .id = "mc-klive", .name = "k-liveness", .family = .computational_mc, .maturity = .engine, .module = "circuit/kliveness", .notes = "" },
    .{ .id = "ctl-bounded", .name = "Bounded CTL", .family = .modal_temporal, .maturity = .fragment, .module = "ctl", .notes = "" },
    .{ .id = "fol-unify", .name = "Robinson unification", .family = .classical_fol, .maturity = .engine, .module = "fol/unify", .notes = "" },
    .{ .id = "fol-fmodel", .name = "Finite model finding", .family = .classical_fol, .maturity = .fragment, .module = "fol/finite_model", .notes = "" },
    .{ .id = "fol-resolution", .name = "Clausal FOL resolution", .family = .computational_atp, .maturity = .fragment, .module = "fol/resolution", .notes = "" },
    .{ .id = "cert-rup", .name = "RUP/DRAT certificates", .family = .metalogic, .maturity = .engine, .module = "sat/drat", .notes = "" },
    .{ .id = "agent-multishot", .name = "Agent multishot SAT", .family = .computational_sat, .maturity = .engine, .module = "agent/session", .notes = "" },
    .{ .id = "modal-k", .name = "Modal logic K", .family = .modal_temporal, .maturity = .fragment, .module = "modal/kripke", .notes = "" },
    .{ .id = "modal-t", .name = "Modal T", .family = .modal_temporal, .maturity = .fragment, .module = "modal/normal", .notes = "" },
    .{ .id = "modal-s4", .name = "Modal S4", .family = .modal_temporal, .maturity = .fragment, .module = "modal/normal", .notes = "" },
    .{ .id = "modal-s5", .name = "Modal S5", .family = .modal_temporal, .maturity = .fragment, .module = "modal/normal", .notes = "" },
    .{ .id = "modal-normal", .name = "Normal modal decision", .family = .modal_temporal, .maturity = .fragment, .module = "modal/normal", .notes = "" },
    .{ .id = "modal-cert", .name = "Modal certificates", .family = .modal_temporal, .maturity = .fragment, .module = "modal/cert", .notes = "validity + countermodel certs with checkers" },
    .{ .id = "tt-mltt-micro", .name = "Martin-Löf type theory (micro)", .family = .type_theory, .maturity = .skeleton, .module = "type_theory/tt", .notes = "" },
    .{ .id = "informal-arg", .name = "Informal argument structure", .family = .informal, .maturity = .fragment, .module = "informal/argument", .notes = "" },
    .{ .id = "intuitionistic-prop", .name = "Intuitionistic propositional", .family = .constructive, .maturity = .fragment, .module = "constructive/intuitionistic", .notes = "" },
    .{ .id = "linear-logic", .name = "Linear logic ILL", .family = .substructural, .maturity = .fragment, .module = "substructural/linear", .notes = "" },
    .{ .id = "relevance-r", .name = "Relevance logic R", .family = .substructural, .maturity = .fragment, .module = "substructural/relevance", .notes = "" },
    .{ .id = "default-logic", .name = "Default / nonmonotonic", .family = .nonmonotonic, .maturity = .fragment, .module = "nonmonotonic/default", .notes = "" },
    .{ .id = "probabilistic", .name = "Probabilistic logic", .family = .probabilistic, .maturity = .fragment, .module = "probabilistic/prob", .notes = "" },
    .{ .id = "markov-logic", .name = "Markov logic networks", .family = .probabilistic, .maturity = .fragment, .module = "probabilistic/markov", .notes = "" },
    .{ .id = "lifted-mln", .name = "Lifted Markov logic", .family = .probabilistic, .maturity = .fragment, .module = "probabilistic/lifted_mln", .notes = "FO weighted + exhaustive grounding" },
    .{ .id = "inductive", .name = "Inductive logic", .family = .inductive_abductive, .maturity = .fragment, .module = "inductive/induction", .notes = "" },
    .{ .id = "abductive", .name = "Abductive reasoning", .family = .inductive_abductive, .maturity = .fragment, .module = "abductive/abduce", .notes = "" },
    .{ .id = "abductive-industrial", .name = "Industrial abduction", .family = .inductive_abductive, .maturity = .fragment, .module = "abductive/industrial", .notes = "" },
    .{ .id = "abductive-mus", .name = "MUS complete abduction", .family = .inductive_abductive, .maturity = .fragment, .module = "abductive/mus", .notes = "" },
    .{ .id = "hol", .name = "Higher-order logic (STLC micro)", .family = .higher_order, .maturity = .fragment, .module = "type_theory/hol", .notes = "" },
    .{ .id = "hol-resolution", .name = "HOL resolution loop", .family = .higher_order, .maturity = .fragment, .module = "type_theory/hol_resolution", .notes = "binary resolve + factor" },
    .{ .id = "description-al", .name = "Description logic ALC", .family = .description_kr, .maturity = .fragment, .module = "description/alc", .notes = "" },
    .{ .id = "description-shiq", .name = "Description logic SHIQ", .family = .description_kr, .maturity = .fragment, .module = "description/shiq", .notes = "" },
    .{ .id = "shiq-tableau", .name = "SHIQ tableau + blocking", .family = .description_kr, .maturity = .fragment, .module = "description/shiq_tableau", .notes = "subset blocking + ALC expansion" },
    .{ .id = "syllogistic", .name = "Aristotelian syllogistic", .family = .historical_term, .maturity = .fragment, .module = "historical/syllogistic", .notes = "" },
    .{ .id = "fuzzy", .name = "Fuzzy / many-valued", .family = .many_valued, .maturity = .fragment, .module = "fuzzy/fuzzy", .notes = "" },
    .{ .id = "paraconsistent", .name = "Paraconsistent LP", .family = .many_valued, .maturity = .fragment, .module = "paraconsistent/lp", .notes = "" },
    .{ .id = "epistemic", .name = "Epistemic logic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic_deontic", .notes = "" },
    .{ .id = "deontic", .name = "Deontic logic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic_deontic", .notes = "" },
    .{ .id = "categorical", .name = "Categorical logic / topos", .family = .algebraic_categorical, .maturity = .fragment, .module = "algebraic/categorical", .notes = "" },
    .{ .id = "ext-cadical", .name = "CaDiCaL (external)", .family = .computational_sat, .maturity = .external, .module = "sat/external", .notes = "" },
    .{ .id = "ext-kissat", .name = "Kissat (external)", .family = .computational_sat, .maturity = .external, .module = "bridge/giants", .notes = "" },
    .{ .id = "ext-z3", .name = "Z3 (external)", .family = .computational_smt, .maturity = .external, .module = "bridge/giants", .notes = "" },
    .{ .id = "ext-abc", .name = "ABC (external)", .family = .computational_mc, .maturity = .external, .module = "bridge/abc_interop", .notes = "" },
    .{ .id = "ext-vampire", .name = "Vampire (external)", .family = .computational_atp, .maturity = .external, .module = "bridge/giants", .notes = "" },

    // PR #2 additional engines (parallel modules; ids do not replace v0.24 rows)
    .{ .id = "abductive-marco", .name = "MARCO-style CNF abduction", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/abduction.zig", .notes = "subset-minimal consistent explanations" },
    .{ .id = "inductive-dnf", .name = "k-term DNF synthesis", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/induction.zig", .notes = "SAT-exact minimal-k" },
    .{ .id = "maxsat", .name = "MaxSAT optimization", .family = .computational_sat, .maturity = .fragment, .module = "sat/maxsat.zig", .notes = "weighted partial" },
    .{ .id = "klm-rational", .name = "KLM rational closure (reason/)", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/klm.zig", .notes = "Lehmann–Magidor ranks" },
    .{ .id = "default-reiter", .name = "Reiter default logic (reason/)", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/default_logic.zig", .notes = "grounded/stable extensions" },
    .{ .id = "dung-af", .name = "Abstract argumentation (Dung)", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/argumentation.zig", .notes = "" },
    .{ .id = "asp-stable", .name = "Answer-set programming", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/asp.zig", .notes = "" },
    .{ .id = "agm-revision", .name = "AGM belief revision", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/agm.zig", .notes = "" },
    .{ .id = "circumscription", .name = "Circumscription", .family = .nonmonotonic, .maturity = .fragment, .module = "reason/circumscription.zig", .notes = "" },
    .{ .id = "analogical", .name = "Analogical reasoning", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/analogy.zig", .notes = "" },
    .{ .id = "alp", .name = "Abductive logic programming", .family = .inductive_abductive, .maturity = .fragment, .module = "reason/alp.zig", .notes = "" },
    .{ .id = "intuitionistic-g4ip", .name = "Intuitionistic G4ip", .family = .constructive, .maturity = .fragment, .module = "logic/intuitionistic.zig", .notes = "Glivenko-verified" },
    .{ .id = "linear-mll", .name = "MLL linear logic", .family = .substructural, .maturity = .fragment, .module = "logic/linear.zig", .notes = "" },
    .{ .id = "dynamic-pdl", .name = "Propositional Dynamic Logic", .family = .modal_temporal, .maturity = .fragment, .module = "modal/pdl.zig", .notes = "" },
    .{ .id = "syllogistic-venn", .name = "Aristotelian syllogistic (Venn)", .family = .historical_term, .maturity = .fragment, .module = "logic/syllogistic.zig", .notes = "" },
    .{ .id = "manyvalued-matrix", .name = "Finite matrices K3/LP/FDE/Ł3", .family = .many_valued, .maturity = .fragment, .module = "logic/manyvalued.zig", .notes = "" },
    .{ .id = "epistemic-s5", .name = "Multi-agent S5 epistemic", .family = .philosophical, .maturity = .fragment, .module = "modal/epistemic.zig", .notes = "" },
    .{ .id = "deontic-sdl", .name = "SDL/KD deontic", .family = .philosophical, .maturity = .fragment, .module = "modal/deontic.zig", .notes = "" },
    .{ .id = "description-el", .name = "EL subsumption", .family = .description_kr, .maturity = .fragment, .module = "logic/el.zig", .notes = "" },
    .{ .id = "cert-rup-checker", .name = "Standalone RUP checker", .family = .metalogic, .maturity = .fragment, .module = "proof/rup_checker.zig", .notes = "" },
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

test "registry v0.23 depth" {
    var n: u32 = 0;
    for (systems) |s| {
        if (std.mem.eql(u8, s.id, "modal-cert") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "shiq-tableau") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "lifted-mln") and s.maturity == .fragment) n += 1;
        if (std.mem.eql(u8, s.id, "hol-resolution") and s.maturity == .fragment) n += 1;
    }
    try std.testing.expect(n == 4);
}
