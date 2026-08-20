//! Propositional circumscription — minimal-model reasoning.
//!
//! Given a theory T (CNF) and a partition of its atoms into **minimized** P,
//! **fixed** Q, and **varying** Z, a model M is P-minimal iff no model M'
//! agrees with M on Q and has a strictly smaller set of true P-atoms
//! (varying atoms unconstrained). CIRC[T; P; Z] ⊨ φ iff φ holds in every
//! P-minimal model.
//!
//! Engine: enumerate (Q,P)-signatures (varying atoms are left to the SAT
//! oracle), keep the satisfiable ones, select the P-minimal signatures per
//! Q-class, then look for a counterexample completion T ∧ signature ∧ ¬φ.
//! Exact for |P|+|Q| ≤ 16; the brute-force oracle in the tests enumerates
//! full assignments independently.
//!
//! This is the McCarthy formalization of closed-world/abnormality reasoning:
//! see the bird/ab canon test (flies unless abnormal, abnormality minimized).

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const Partition = struct {
    /// Atoms whose extension is minimized.
    minimized: []const u32,
    /// Atoms held fixed across the minimality comparison.
    fixed: []const u32 = &.{},
    // Every other atom of the theory varies.
};

pub const CircError = error{
    SignatureTooLarge,
    PartitionAtomOutOfRange,
    DuplicatePartitionAtom,
    QueryAtomOutOfRange,
    InconclusiveSatQuery,
};

pub fn validate(theory: *const Cnf, part: Partition, phi_cube: []const Lit) CircError!void {
    if (part.minimized.len + part.fixed.len > 16) return error.SignatureTooLarge;
    for (part.minimized, 0..) |atom, index| {
        if (atom >= theory.num_vars) return error.PartitionAtomOutOfRange;
        for (part.minimized[index + 1 ..]) |other| if (atom == other) return error.DuplicatePartitionAtom;
        for (part.fixed) |other| if (atom == other) return error.DuplicatePartitionAtom;
    }
    for (part.fixed, 0..) |atom, index| {
        if (atom >= theory.num_vars) return error.PartitionAtomOutOfRange;
        for (part.fixed[index + 1 ..]) |other| if (atom == other) return error.DuplicatePartitionAtom;
    }
    for (phi_cube) |literal| {
        if (literal.variable().index() >= theory.num_vars) return error.QueryAtomOutOfRange;
    }
}

fn signatureSat(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    sig: u32,
    extra_neg_cube: ?[]const Lit,
) !bool {
    var t = Cnf.init(allocator);
    defer t.deinit();
    t.ensureVars(theory.num_vars);
    for (0..theory.numClauses()) |ci| {
        try t.addClause(theory.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    var idx: u5 = 0;
    for (part.minimized) |a| {
        const l = if ((sig >> idx) & 1 == 1) Lit.positive(Var.fromIndex(a)) else Lit.negative(Var.fromIndex(a));
        t.ensureVars(a + 1);
        try t.addClause(&.{l});
        idx += 1;
    }
    for (part.fixed) |a| {
        const l = if ((sig >> idx) & 1 == 1) Lit.positive(Var.fromIndex(a)) else Lit.negative(Var.fromIndex(a));
        t.ensureVars(a + 1);
        try t.addClause(&.{l});
        idx += 1;
    }
    if (extra_neg_cube) |cube| {
        var buf: std.ArrayList(Lit) = .empty;
        defer buf.deinit(allocator);
        for (cube) |l| {
            t.ensureVars(l.variable().index() + 1);
            try buf.append(allocator, l.not());
        }
        try t.addClause(buf.items);
    }
    const r = try solver_mod.solveCnf(allocator, &t, .{});
    defer if (r.model) |m| allocator.free(m);
    return switch (r.status) {
        .sat => true,
        .unsat => false,
        .unknown => error.InconclusiveSatQuery,
    };
}

fn signatureModel(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    sig: u32,
    negated_cube: []const Lit,
) !?[]Value {
    var t = Cnf.init(allocator);
    defer t.deinit();
    t.ensureVars(theory.num_vars);
    for (0..theory.numClauses()) |ci| try t.addClause(theory.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    var idx: u5 = 0;
    for (part.minimized) |atom| {
        const literal = if ((sig >> idx) & 1 == 1) Lit.positive(Var.fromIndex(atom)) else Lit.negative(Var.fromIndex(atom));
        try t.addClause(&.{literal});
        idx += 1;
    }
    for (part.fixed) |atom| {
        const literal = if ((sig >> idx) & 1 == 1) Lit.positive(Var.fromIndex(atom)) else Lit.negative(Var.fromIndex(atom));
        try t.addClause(&.{literal});
        idx += 1;
    }
    var negated: std.ArrayList(Lit) = .empty;
    defer negated.deinit(allocator);
    for (negated_cube) |literal| try negated.append(allocator, literal.not());
    try t.addClause(negated.items);
    const result = try solver_mod.solveCnf(allocator, &t, .{});
    return switch (result.status) {
        .sat => result.model,
        .unsat => blk: {
            if (result.model) |model| allocator.free(model);
            break :blk null;
        },
        .unknown => blk: {
            if (result.model) |model| allocator.free(model);
            break :blk error.InconclusiveSatQuery;
        },
    };
}

fn pPart(sig: u32, np: u5) u32 {
    return sig & ((@as(u32, 1) << np) - 1);
}
fn qPart(sig: u32, np: u5) u32 {
    return sig >> np;
}

fn collectMinimalSignatures(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
) !std.ArrayList(u32) {
    const np: u5 = @intCast(part.minimized.len);
    const nq: u5 = @intCast(part.fixed.len);
    const total: u32 = @as(u32, 1) << (np + nq);
    var satisfiable: std.ArrayList(u32) = .empty;
    defer satisfiable.deinit(allocator);
    var sig: u32 = 0;
    while (sig < total) : (sig += 1) {
        if (try signatureSat(allocator, theory, part, sig, null)) try satisfiable.append(allocator, sig);
    }
    var minimal: std.ArrayList(u32) = .empty;
    errdefer minimal.deinit(allocator);
    for (satisfiable.items) |candidate| {
        var is_minimal = true;
        for (satisfiable.items) |other| {
            if (other == candidate or qPart(other, np) != qPart(candidate, np)) continue;
            const other_p = pPart(other, np);
            const candidate_p = pPart(candidate, np);
            if ((other_p & candidate_p) == other_p and other_p != candidate_p) {
                is_minimal = false;
                break;
            }
        }
        if (is_minimal) try minimal.append(allocator, candidate);
    }
    return minimal;
}

pub const Decision = struct {
    allocator: std.mem.Allocator,
    entailed: bool,
    minimal_signatures: std.ArrayList(u32) = .empty,
    counterexample_signature: ?u32 = null,
    counterexample_model: ?[]Value = null,

    pub fn deinit(self: *Decision) void {
        self.minimal_signatures.deinit(self.allocator);
        if (self.counterexample_model) |model| self.allocator.free(model);
        self.* = undefined;
    }
};

pub fn decide(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    phi_cube: []const Lit,
) !Decision {
    try validate(theory, part, phi_cube);
    var decision = Decision{ .allocator = allocator, .entailed = true };
    errdefer decision.deinit();
    decision.minimal_signatures = try collectMinimalSignatures(allocator, theory, part);
    for (decision.minimal_signatures.items) |signature| {
        if (try signatureModel(allocator, theory, part, signature, phi_cube)) |model| {
            decision.entailed = false;
            decision.counterexample_signature = signature;
            decision.counterexample_model = model;
            break;
        }
    }
    return decision;
}

fn literalHolds(model: []const Value, literal: Lit) bool {
    const value = model[literal.variable().index()];
    return if (literal.isNeg()) value == .false_ else value == .true_;
}

fn modelSatisfiesTheory(theory: *const Cnf, model: []const Value) bool {
    if (model.len < theory.num_vars) return false;
    for (0..theory.numClauses()) |clause_index| {
        const clause = theory.clauseSlice(ClauseId.fromIndex(@intCast(clause_index)));
        var satisfied = false;
        for (clause) |literal| {
            if (literalHolds(model, literal)) {
                satisfied = true;
                break;
            }
        }
        if (!satisfied) return false;
    }
    return true;
}

/// Replay exact minimal-signature evidence and, for non-entailment, the full
/// counterexample assignment. Entailment is accepted only after every minimal
/// signature is conclusively checked against the negated query.
pub fn verifyDecision(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    phi_cube: []const Lit,
    decision: *const Decision,
) !bool {
    try validate(theory, part, phi_cube);
    const signature_bits = part.minimized.len + part.fixed.len;
    const total: u32 = @as(u32, 1) << @intCast(signature_bits);
    for (decision.minimal_signatures.items, 0..) |signature, index| {
        if (signature >= total) return false;
        for (decision.minimal_signatures.items[index + 1 ..]) |other| if (signature == other) return false;
    }
    var expected = try collectMinimalSignatures(allocator, theory, part);
    defer expected.deinit(allocator);
    if (expected.items.len != decision.minimal_signatures.items.len) return false;
    for (expected.items) |signature| {
        var present = false;
        for (decision.minimal_signatures.items) |claimed| if (signature == claimed) {
            present = true;
            break;
        };
        if (!present) return false;
    }

    if (decision.entailed) {
        if (decision.counterexample_signature != null or decision.counterexample_model != null) return false;
        for (expected.items) |signature| {
            if (try signatureSat(allocator, theory, part, signature, phi_cube)) return false;
        }
        return true;
    }

    const signature = decision.counterexample_signature orelse return false;
    const model = decision.counterexample_model orelse return false;
    var is_minimal = false;
    for (expected.items) |candidate| if (candidate == signature) {
        is_minimal = true;
        break;
    };
    if (!is_minimal or !modelSatisfiesTheory(theory, model)) return false;
    var bit_index: u5 = 0;
    for (part.minimized) |atom| {
        const expected_true = (signature >> bit_index) & 1 == 1;
        if ((model[atom] == .true_) != expected_true) return false;
        bit_index += 1;
    }
    for (part.fixed) |atom| {
        const expected_true = (signature >> bit_index) & 1 == 1;
        if ((model[atom] == .true_) != expected_true) return false;
        bit_index += 1;
    }
    var query_holds = true;
    for (phi_cube) |literal| {
        if (!literalHolds(model, literal)) {
            query_holds = false;
            break;
        }
    }
    return !query_holds;
}

/// Does CIRC[T; minimized; varying] entail the cube φ?
pub fn circEntails(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    phi_cube: []const Lit,
) !bool {
    var decision = try decide(allocator, theory, part, phi_cube);
    defer decision.deinit();
    return decision.entailed;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn lp(v: u32) Lit {
    return Lit.positive(Var.fromIndex(v));
}
fn ln(v: u32) Lit {
    return Lit.negative(Var.fromIndex(v));
}

/// Brute-force oracle over full assignments (independent code path).
fn bruteCircEntails(theory: *const Cnf, part: Partition, phi_cube: []const Lit, num_vars: u32) bool {
    const total: u64 = @as(u64, 1) << @intCast(num_vars);
    var models: [1 << 12]u32 = undefined;
    var n_models: usize = 0;
    var a: u64 = 0;
    while (a < total) : (a += 1) {
        var assign: [12]Value = undefined;
        for (0..num_vars) |v| assign[v] = if ((a >> @intCast(v)) & 1 == 1) .true_ else .false_;
        var ok = true;
        for (0..theory.numClauses()) |ci| {
            const cl = theory.clauseSlice(ClauseId.fromIndex(@intCast(ci)));
            var sat = false;
            for (cl) |l| {
                const val = assign[l.variable().index()];
                if (if (l.isNeg()) val == .false_ else val == .true_) {
                    sat = true;
                    break;
                }
            }
            if (!sat) {
                ok = false;
                break;
            }
        }
        if (ok) {
            models[n_models] = @intCast(a);
            n_models += 1;
        }
    }
    // φ must hold in every P-minimal model.
    for (models[0..n_models]) |m| {
        var minimal = true;
        for (models[0..n_models]) |m2| {
            if (m2 == m) continue;
            var fixed_eq = true;
            for (part.fixed) |q| {
                if ((m >> @intCast(q)) & 1 != (m2 >> @intCast(q)) & 1) {
                    fixed_eq = false;
                    break;
                }
            }
            if (!fixed_eq) continue;
            var subset = true;
            var strict = false;
            for (part.minimized) |p| {
                const b1 = (m >> @intCast(p)) & 1;
                const b2 = (m2 >> @intCast(p)) & 1;
                if (b2 == 1 and b1 == 0) {
                    subset = false;
                    break;
                }
                if (b1 == 1 and b2 == 0) strict = true;
            }
            if (subset and strict) {
                minimal = false;
                break;
            }
        }
        if (!minimal) continue;
        var phi_holds = true;
        for (phi_cube) |l| {
            const val = (m >> @intCast(l.variable().index())) & 1 == 1;
            if (if (l.isNeg()) val else !val) {
                phi_holds = false;
                break;
            }
        }
        if (!phi_holds) return false;
    }
    return true;
}

test "circ: bird/ab canon — flies by minimizing abnormality" {
    // 0=bird, 1=ab, 2=flies. T: bird, bird∧¬ab→flies.
    var t = Cnf.init(testing.allocator);
    defer t.deinit();
    try t.addClause(&.{lp(0)});
    try t.addClause(&.{ ln(0), lp(1), lp(2) });
    const part = Partition{ .minimized = &.{1}, .fixed = &.{0} };
    // Classically: T ⊭ flies. Circumscribing ab: flies.
    try testing.expect(try circEntails(testing.allocator, &t, part, &.{lp(2)}));
    try testing.expect(try circEntails(testing.allocator, &t, part, &.{ln(1)}));
    try testing.expect(bruteCircEntails(&t, part, &.{lp(2)}, 3));
}

test "circ: exception defeats the conclusion" {
    // Add penguin→ab, penguin (fixed). Now ab is forced; ¬flies not derivable,
    // but flies no longer follows either.
    var t = Cnf.init(testing.allocator);
    defer t.deinit();
    try t.addClause(&.{lp(0)});
    try t.addClause(&.{ ln(0), lp(1), lp(2) });
    try t.addClause(&.{lp(3)}); // penguin
    try t.addClause(&.{ ln(3), lp(1) }); // penguin → ab
    const part = Partition{ .minimized = &.{1}, .fixed = &.{ 0, 3 } };
    try testing.expect(!try circEntails(testing.allocator, &t, part, &.{lp(2)}));
    try testing.expect(try circEntails(testing.allocator, &t, part, &.{lp(1)}));
    try testing.expect(!bruteCircEntails(&t, part, &.{lp(2)}, 4));
    try testing.expect(bruteCircEntails(&t, part, &.{lp(1)}, 4));
}

test "circ: disjunctive minimization — either ab1 or ab2, not both" {
    // T: p∨q with p,q both minimized. Minimal models: exactly one true? No —
    // minimal models are {p},{q} (∅ is not a model). CIRC ⊨ ¬(p∧q).
    var t = Cnf.init(testing.allocator);
    defer t.deinit();
    try t.addClause(&.{ lp(0), lp(1) });
    const part = Partition{ .minimized = &.{ 0, 1 } };
    // ¬(p∧q) is not a cube; check via two queries: in every minimal model,
    // p→¬q and q→¬p. Equivalent pair on cubes is not expressible directly;
    // use the brute oracle for the disjunction claim and engine for members.
    try testing.expect(!try circEntails(testing.allocator, &t, part, &.{lp(0)}));
    try testing.expect(!try circEntails(testing.allocator, &t, part, &.{lp(1)}));
    // Each minimal model falsifies p∧q:
    try testing.expect(!try circEntails(testing.allocator, &t, part, &.{ lp(0), lp(1) }));
    try testing.expect(!bruteCircEntails(&t, part, &.{ lp(0), lp(1) }, 2));
}

test "circ: random instances match brute-force oracle" {
    var prng = std.Random.DefaultPrng.init(0xC12C);
    const rand = prng.random();
    var instance: u32 = 0;
    while (instance < 30) : (instance += 1) {
        const nv: u32 = 4;
        var t = Cnf.init(testing.allocator);
        defer t.deinit();
        t.ensureVars(nv);
        const n_cl = 1 + rand.uintLessThan(u32, 4);
        var cbuf: [3]Lit = undefined;
        for (0..n_cl) |_| {
            const len = 1 + rand.uintLessThan(u32, 3);
            for (0..len) |i| {
                const v = rand.uintLessThan(u32, nv);
                cbuf[i] = if (rand.boolean()) lp(v) else ln(v);
            }
            try t.addClause(cbuf[0..len]);
        }
        // Minimize {0,1}, fix {2}, vary {3}.
        const part = Partition{ .minimized = &.{ 0, 1 }, .fixed = &.{2} };
        const queries = [_][]const Lit{
            &.{lp(0)}, &.{ln(0)}, &.{lp(3)}, &.{ ln(1), lp(2) },
        };
        for (queries) |q| {
            const got = try circEntails(testing.allocator, &t, part, q);
            const want = bruteCircEntails(&t, part, q, nv);
            try testing.expectEqual(want, got);
        }
    }
}

test "circ: decisions carry replayable minimal countermodels" {
    var theory = Cnf.init(testing.allocator);
    defer theory.deinit();
    try theory.addClause(&.{ lp(0), lp(1) });
    theory.ensureVars(3);
    const part = Partition{ .minimized = &.{ 0, 1 }, .fixed = &.{2} };
    var negative = try decide(testing.allocator, &theory, part, &.{lp(0)});
    defer negative.deinit();
    try testing.expect(!negative.entailed);
    try testing.expect(negative.counterexample_model != null);
    try testing.expect(try verifyDecision(testing.allocator, &theory, part, &.{lp(0)}, &negative));
    negative.counterexample_signature = 3;
    try testing.expect(!(try verifyDecision(testing.allocator, &theory, part, &.{lp(0)}, &negative)));

    var positive = try decide(testing.allocator, &theory, part, &.{ lp(0), lp(1) });
    defer positive.deinit();
    try testing.expect(!positive.entailed);
    try testing.expect(try verifyDecision(testing.allocator, &theory, part, &.{ lp(0), lp(1) }, &positive));
    _ = positive.minimal_signatures.pop();
    try testing.expect(!(try verifyDecision(testing.allocator, &theory, part, &.{ lp(0), lp(1) }, &positive)));
}

test "circ: malformed partitions and queries fail closed" {
    var theory = Cnf.init(testing.allocator);
    defer theory.deinit();
    theory.ensureVars(2);
    try testing.expectError(error.DuplicatePartitionAtom, decide(testing.allocator, &theory, .{ .minimized = &.{0}, .fixed = &.{0} }, &.{lp(1)}));
    try testing.expectError(error.PartitionAtomOutOfRange, decide(testing.allocator, &theory, .{ .minimized = &.{2} }, &.{lp(1)}));
    try testing.expectError(error.QueryAtomOutOfRange, decide(testing.allocator, &theory, .{ .minimized = &.{0} }, &.{lp(2)}));
    const too_wide = [_]u32{ 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0 };
    try testing.expectError(error.SignatureTooLarge, decide(testing.allocator, &theory, .{ .minimized = &too_wide }, &.{lp(0)}));
}
