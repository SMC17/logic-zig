//! Evidence-bearing contracts for the executable museum of logic.
//!
//! A named system is not a complete exhibit because a registry row says so.
//! Promotion is derived from dimension claims, executable evidence references,
//! and an explicit decidability/completeness boundary.

const std = @import("std");
const registry = @import("registry.zig");

pub const Coverage = enum { absent, cataloged, partial, complete };
pub const EvidenceLevel = enum { none, sketch, compiled, unit_tested, integration_tested, audited };
pub const Decidability = enum { decidable, semidecidable, undecidable, bounded };
pub const Promotion = enum { cataloged, specified, kernel_complete, automation_complete, verified_exhibit };

pub const Claim = struct {
    coverage: Coverage,
    evidence: EvidenceLevel,
    specification: []const u8,
    tests: []const []const u8,

    pub fn evidenced(self: Claim) bool {
        return self.coverage != .absent and self.evidence != .none and
            self.specification.len > 0 and self.tests.len > 0;
    }

    pub fn completeAndEvidenced(self: Claim) bool {
        return self.coverage == .complete and self.evidenced();
    }
};

pub const ExhibitManifest = struct {
    id: []const u8,
    name: []const u8,
    formal_identity: []const u8,
    contract_version: []const u8,
    decidability: Decidability,
    completeness_scope: []const u8,
    limitations: []const []const u8,
    syntax: Claim,
    semantics: Claim,
    calculus: Claim,
    automation: Claim,
    proof_objects: Claim,
    countermodels: Claim,
    documentation: Claim,
    interoperability: Claim,

    pub fn validate(self: ExhibitManifest) !void {
        if (self.id.len == 0 or self.name.len == 0 or self.formal_identity.len == 0 or
            self.contract_version.len == 0 or self.completeness_scope.len == 0)
            return error.IncompleteIdentity;
        inline for (.{ self.syntax, self.semantics, self.calculus, self.automation, self.proof_objects, self.countermodels, self.documentation, self.interoperability }) |dimension| {
            if (dimension.coverage != .absent and !dimension.evidenced()) return error.UnevidencedClaim;
        }
    }

    pub fn promotion(self: ExhibitManifest) Promotion {
        self.validate() catch return .cataloged;
        if (!self.syntax.completeAndEvidenced() or !self.semantics.completeAndEvidenced())
            return .cataloged;
        if (!self.calculus.completeAndEvidenced()) return .specified;
        if (!self.automation.completeAndEvidenced()) return .kernel_complete;
        if (!self.proof_objects.completeAndEvidenced() or
            !self.countermodels.completeAndEvidenced() or
            !self.documentation.completeAndEvidenced()) return .automation_complete;
        return .verified_exhibit;
    }
};

const none = [_][]const u8{};
const prop_tests = [_][]const u8{
    "src/ir/expr.zig",
    "src/pass/tseitin.zig",
    "src/sat/solver.zig",
    "src/sat/drat.zig",
    "src/proof/rup_checker.zig",
    "tests/integration_test.zig",
};
const syllogistic_tests = [_][]const u8{"src/logic/syllogistic.zig"};
const matrix_tests = [_][]const u8{"src/logic/manyvalued.zig"};
const dung_tests = [_][]const u8{"src/reason/argumentation.zig"};
const asp_tests = [_][]const u8{"src/reason/asp.zig"};
const default_tests = [_][]const u8{"src/reason/default_logic.zig"};
const agm_tests = [_][]const u8{"src/reason/agm.zig"};
const circ_tests = [_][]const u8{"src/reason/circumscription.zig"};
const modal_tests = [_][]const u8{"src/modal/kripke.zig"};
const fol_term_tests = [_][]const u8{ "src/fol/term.zig", "src/fol/unify.zig" };
const fol_resolution_tests = [_][]const u8{"src/fol/resolution.zig"};
const fol_model_tests = [_][]const u8{ "src/fol/finite_model.zig", "src/fol/finite_model_sat.zig" };

fn claim(coverage: Coverage, evidence: EvidenceLevel, spec: []const u8, tests: []const []const u8) Claim {
    return .{ .coverage = coverage, .evidence = evidence, .specification = spec, .tests = tests };
}

/// Representative contracts deliberately expose gaps instead of flattening
/// unlike notions of completeness into one maturity label.
pub const exhibits = [_]ExhibitManifest{
    .{
        .id = "prop-classical",
        .name = "Classical propositional logic",
        .formal_identity = "Two-valued classical propositional logic with truth-functional semantics",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Parsed formulas, executable semantics, Tseitin CNF, CDCL decision, models and RUP evidence",
        .limitations = &.{ "The serialized checker is audited by tests, not formally verified", "RUP checking does not accept arbitrary RAT/FRAT/LRAT inputs" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .automation = claim(.complete, .integration_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .proof_objects = claim(.complete, .integration_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/prop-classical.md", &prop_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/prop-classical.md", &prop_tests),
        .interoperability = claim(.partial, .integration_tested, "docs/INDUSTRIAL.md#ipasir", &prop_tests),
    },
    .{
        .id = "syllogistic",
        .name = "Aristotelian categorical syllogistic",
        .formal_identity = "A/E/I/O categorical syllogisms over S, M, P in four figures",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "All 256 forms under Boolean and three-term existential-import semantics",
        .limitations = &.{ "No relational or modal syllogisms", "No natural-language parser", "Medieval supposition is a separate future exhibit" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/syllogistic.md", &syllogistic_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "matrix-k3",
        .name = "Strong Kleene K3",
        .formal_identity = "Three-valued Strong Kleene matrix with only true designated",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Finite propositional K3 consequence for negation, conjunction, disjunction, and material implication",
        .limitations = &.{ "At most eight atoms per decision", "No quantified extension" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "matrix-lp",
        .name = "Priest LP",
        .formal_identity = "Three-valued Logic of Paradox with glut and true designated",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Finite propositional LP consequence for the implemented matrix",
        .limitations = &.{ "At most eight atoms per decision", "No quantified extension" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "matrix-fde",
        .name = "Belnap-Dunn FDE",
        .formal_identity = "Four-valued First-Degree Entailment with true and both designated",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Finite propositional FDE consequence for the implemented bilattice matrix",
        .limitations = &.{ "At most eight atoms per decision", "No quantified extension" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "matrix-l3",
        .name = "Lukasiewicz L3",
        .formal_identity = "Three-valued Lukasiewicz matrix with implication min(1,1-a+b)",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Finite propositional L3 consequence for the implemented matrix",
        .limitations = &.{ "At most eight atoms per decision", "No continuum-valued extension" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/finite-matrices.md", &matrix_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "dung-af",
        .name = "Dung abstract argumentation",
        .formal_identity = "Finite abstract argumentation frameworks with conflict-free, defense-based and stable semantics",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Exact admissible, complete, grounded, stable and preferred extensions plus credulous and skeptical acceptance for finite AFs of at most 20 arguments",
        .limitations = &.{ "Exponential subset enumeration", "No ICCMA parser or competition-scale specialized algorithms", "No semi-stable, stage, ideal or value-based semantics" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/dung-argumentation.md", &dung_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "asp-stable",
        .name = "Propositional normal answer-set programming",
        .formal_identity = "Stable-model semantics for finite propositional normal logic programs with integrity constraints",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Exact stable-model enumeration and reduct replay for validated normal programs with at most 16 atoms by default and an absolute supported limit of 20",
        .limitations = &.{ "Exponential subset enumeration", "No variables or grounding", "No disjunctive heads, classical negation, aggregates, weak constraints or optimization", "No ASP-Core-2 parser or clingo-scale claim" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/asp-stable.md", &asp_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/asp-stable.md", &asp_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "default-logic",
        .name = "Finite propositional Reiter default logic",
        .formal_identity = "Reiter extensions for finite propositional default theories with CNF facts and cube prerequisites, justifications and consequents",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Exact grounded stable generating-set enumeration and skeptical or credulous cube consequence for at most 20 defaults",
        .limitations = &.{ "Exponential generating-set enumeration", "Default components are literal cubes rather than arbitrary formulas", "No first-order defaults, parser, priorities, autoepistemic translation or industrial solver" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/reiter-default-logic.md", &default_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "agm-revision",
        .name = "Finite AGM base contraction and revision",
        .formal_identity = "Partial-meet contraction of finite propositional belief bases and Levi-identity revision",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Exact remainder families and maxichoice, full-meet or maximum-cardinality contraction and cube revision for bases of at most 16 CNF beliefs",
        .limitations = &.{ "Exponential sub-base enumeration", "Syntax-sensitive finite belief bases rather than deductively closed theories", "Revision inputs are literal cubes", "No epistemic entrenchment, iterated-revision policy or belief-merging interoperability" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/agm-base-change.md", &agm_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/agm-base-change.md", &agm_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "circumscription",
        .name = "Finite propositional circumscription",
        .formal_identity = "McCarthy-style propositional minimal-model entailment with minimized, fixed and varying atoms",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Exact P-minimal signature enumeration and cube entailment for CNF theories with at most 16 minimized plus fixed atoms",
        .limitations = &.{ "Exponential signature enumeration", "Queries are literal cubes", "No first-order or predicate circumscription", "No prioritized, parallel or nested circumscription syntax", "No industrial minimal-model solver" },
        .syntax = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .semantics = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .calculus = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .automation = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .proof_objects = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .countermodels = claim(.complete, .unit_tested, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .documentation = claim(.complete, .audited, "docs/exhibits/propositional-circumscription.md", &circ_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "modal-s4",
        .name = "Modal propositional logic S4",
        .formal_identity = "Normal modal logic S4 over reflexive and transitive Kripke frames",
        .contract_version = "0.1.0",
        .decidability = .decidable,
        .completeness_scope = "Finite-frame formula evaluation only",
        .limitations = &.{ "No parser", "No complete tableau or decision procedure", "No proof objects" },
        .syntax = claim(.partial, .unit_tested, "docs/TAXONOMY_COVERAGE.md", &modal_tests),
        .semantics = claim(.partial, .unit_tested, "docs/TAXONOMY_COVERAGE.md", &modal_tests),
        .calculus = claim(.absent, .none, "", &none),
        .automation = claim(.absent, .none, "", &none),
        .proof_objects = claim(.absent, .none, "", &none),
        .countermodels = claim(.partial, .unit_tested, "docs/TAXONOMY_COVERAGE.md", &modal_tests),
        .documentation = claim(.partial, .sketch, "docs/TAXONOMY_COVERAGE.md", &modal_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
    .{
        .id = "fol-classical-equality",
        .name = "Classical first-order logic with equality",
        .formal_identity = "Classical many-sorted first-order target; current implementation is an untyped clausal subset",
        .contract_version = "0.1.0",
        .decidability = .semidecidable,
        .completeness_scope = "Term/formula representation, unification, partial resolution, bounded finite-model search",
        .limitations = &.{ "No full parser or clausifier", "Resolution search is incomplete", "Function/predicate arity is limited to two", "No proof DAG" },
        .syntax = claim(.partial, .unit_tested, "docs/INDUSTRIAL.md#first-order", &fol_term_tests),
        .semantics = claim(.partial, .unit_tested, "docs/INDUSTRIAL.md#first-order", &fol_model_tests),
        .calculus = claim(.partial, .unit_tested, "docs/INDUSTRIAL.md#first-order", &fol_resolution_tests),
        .automation = claim(.partial, .unit_tested, "docs/INDUSTRIAL.md#first-order", &fol_resolution_tests),
        .proof_objects = claim(.absent, .none, "", &none),
        .countermodels = claim(.partial, .unit_tested, "docs/INDUSTRIAL.md#first-order", &fol_model_tests),
        .documentation = claim(.partial, .sketch, "docs/INDUSTRIAL.md#first-order", &fol_term_tests),
        .interoperability = claim(.absent, .none, "", &none),
    },
};

pub fn printMuseum() void {
    std.debug.print("=== EXECUTABLE LOGIC MUSEUM ({d} contracted exhibits) ===\n", .{exhibits.len});
    for (exhibits) |exhibit| {
        std.debug.print("{s:22} {s:20} {s}\n", .{ @tagName(exhibit.promotion()), exhibit.id, exhibit.name });
        std.debug.print("  scope: {s}\n", .{exhibit.completeness_scope});
        for (exhibit.limitations) |limitation| std.debug.print("  limit: {s}\n", .{limitation});
    }
    var catalog_only: u32 = 0;
    for (registry.systems) |system| {
        var contracted = false;
        for (exhibits) |exhibit| {
            if (std.mem.eql(u8, exhibit.id, system.id)) {
                contracted = true;
                break;
            }
        }
        if (!contracted) catalog_only += 1;
    }
    std.debug.print("--- catalog-only restoration backlog ({d}) ---\n", .{catalog_only});
    for (registry.systems) |system| {
        var contracted = false;
        for (exhibits) |exhibit| {
            if (std.mem.eql(u8, exhibit.id, system.id)) {
                contracted = true;
                break;
            }
        }
        if (!contracted) std.debug.print("{s:22} {s:20} {s}\n", .{ "catalog_only", system.id, system.name });
    }
}

test "all exhibit claims are structurally evidenced" {
    for (exhibits, 0..) |exhibit, index| {
        try exhibit.validate();
        for (exhibits[index + 1 ..]) |other| {
            try std.testing.expect(!std.mem.eql(u8, exhibit.id, other.id));
        }
    }
}

test "promotion is derived and fail closed" {
    try std.testing.expectEqual(Promotion.verified_exhibit, exhibits[0].promotion());
    try std.testing.expectEqual(Promotion.verified_exhibit, exhibits[1].promotion());
    for (exhibits[2..11]) |exhibit| try std.testing.expectEqual(Promotion.verified_exhibit, exhibit.promotion());
    try std.testing.expectEqual(Promotion.cataloged, exhibits[11].promotion());
    try std.testing.expectEqual(Promotion.cataloged, exhibits[12].promotion());

    var bad = exhibits[0];
    bad.syntax = claim(.complete, .none, "", &none);
    try std.testing.expectEqual(Promotion.cataloged, bad.promotion());
    try std.testing.expectError(error.UnevidencedClaim, bad.validate());
}
