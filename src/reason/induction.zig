//! Inductive synthesis — examples → rule, with deduction as the oracle.
//!
//! Learns a k-term DNF hypothesis over boolean features consistent with all
//! labeled examples, by exact SAT encoding and iterative deepening on k
//! (Occam preference: the first k that admits a consistent hypothesis).
//!
//! Encoding for fixed k over n features:
//!   p(t,j)  — term t selects literal j (j = 2f positive, 2f+1 negated)
//!   a(t,e)  — term t accepts positive example e
//! Constraints:
//!   every negative example is rejected by every term
//!     (each term selects at least one literal the example falsifies);
//!   every positive example is accepted by some term
//!     (a(t,e) → t selects no literal the example falsifies; ∨_t a(t,e)).
//! The encoding is exact: SAT ⇔ a consistent k-term DNF exists, so an UNSAT
//! answer at k−1 certifies minimality of k (when solved without budget cuts).
//!
//! This is general inductive inference on the propositional slice — not
//! k-induction over transition systems (see `circuit/kinduction.zig`).

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const Example = struct {
    features: []const bool,
    label: bool,
};

pub const TermLit = struct {
    feature: u32,
    negated: bool,
};

pub const InduceStatus = enum {
    /// Consistent hypothesis found and re-verified on every example.
    learned,
    /// No consistent k-term DNF exists for any k ≤ max_k (proven).
    no_hypothesis,
    /// Conflict budget exhausted before an answer.
    unknown,
};

pub const Options = struct {
    /// Largest number of DNF terms to try.
    max_k: u32 = 4,
    /// CDCL conflict budget per synthesis call.
    max_conflicts: u64 = 500_000,
};

pub const Result = struct {
    allocator: std.mem.Allocator,
    status: InduceStatus,
    /// Learned DNF: disjunction of terms; each term a conjunction of literals.
    /// Empty term list ≡ false; empty term ≡ true. Owned.
    terms: [][]TermLit = &.{},
    k_used: u32 = 0,
    /// True when every k' < k_used was *proven* to admit no consistent hypothesis.
    minimal: bool = false,
    /// Deductive re-check: hypothesis evaluated on every example matched its label.
    verified: bool = false,

    pub fn deinit(self: *Result) void {
        for (self.terms) |t| self.allocator.free(t);
        self.allocator.free(self.terms);
        self.* = undefined;
    }
};

/// Evaluate a DNF hypothesis on a feature vector.
pub fn evaluate(terms: []const []const TermLit, features: []const bool) bool {
    for (terms) |t| {
        var ok = true;
        for (t) |l| {
            const v = features[l.feature];
            if (if (l.negated) v else !v) {
                ok = false;
                break;
            }
        }
        if (ok) return true;
    }
    return false;
}

pub fn induceDnf(
    allocator: std.mem.Allocator,
    num_features: u32,
    examples: []const Example,
    opts: Options,
) !Result {
    for (examples) |e| std.debug.assert(e.features.len == num_features);

    // Contradictory labels on identical vectors → no hypothesis at any k.
    for (examples, 0..) |e1, i| {
        for (examples[i + 1 ..]) |e2| {
            if (e1.label != e2.label and std.mem.eql(bool, e1.features, e2.features)) {
                return .{ .allocator = allocator, .status = .no_hypothesis };
            }
        }
    }

    var num_pos: u32 = 0;
    for (examples) |e| {
        if (e.label) num_pos += 1;
    }
    if (num_pos == 0) {
        // Empty DNF (false) rejects every negative example.
        var r = Result{ .allocator = allocator, .status = .learned, .minimal = true };
        r.terms = try allocator.alloc([]TermLit, 0);
        r.verified = verify(&r, examples);
        return r;
    }

    var all_smaller_proven_unsat = true;
    var k: u32 = 1;
    while (k <= opts.max_k) : (k += 1) {
        var enc = try encode(allocator, num_features, examples, num_pos, k);
        defer enc.deinit();
        var sr = try solver_mod.solveCnf(allocator, &enc, .{
            .max_conflicts = opts.max_conflicts,
        });
        defer if (sr.model) |m| allocator.free(m);
        defer if (sr.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        switch (sr.status) {
            .sat => {
                var r = Result{
                    .allocator = allocator,
                    .status = .learned,
                    .k_used = k,
                    .minimal = all_smaller_proven_unsat,
                };
                r.terms = try decode(allocator, num_features, k, sr.model.?);
                r.verified = verify(&r, examples);
                return r;
            },
            .unsat => {},
            .unknown => all_smaller_proven_unsat = false,
        }
    }
    return .{
        .allocator = allocator,
        .status = if (all_smaller_proven_unsat) .no_hypothesis else .unknown,
    };
}

fn pVar(num_features: u32, t: u32, j: u32) Lit {
    return Lit.positive(Var.fromIndex(t * 2 * num_features + j));
}

fn aVar(num_features: u32, k: u32, t: u32, pi: u32) Lit {
    return Lit.positive(Var.fromIndex(k * 2 * num_features + pi * k + t));
}

/// Literal j is falsified by feature vector fv (selecting it rejects fv).
fn falsifies(fv: []const bool, j: u32) bool {
    const f = j / 2;
    const negated = (j & 1) == 1;
    return if (negated) fv[f] else !fv[f];
}

fn encode(
    allocator: std.mem.Allocator,
    num_features: u32,
    examples: []const Example,
    num_pos: u32,
    k: u32,
) !Cnf {
    var out = Cnf.init(allocator);
    errdefer out.deinit();
    out.ensureVars(k * 2 * num_features + num_pos * k);

    var buf: std.ArrayList(Lit) = .empty;
    defer buf.deinit(allocator);

    var pi: u32 = 0;
    for (examples) |e| {
        if (e.label) {
            // Some term accepts e.
            buf.clearRetainingCapacity();
            for (0..k) |t| try buf.append(allocator, aVar(num_features, k, @intCast(t), pi));
            try out.addClause(buf.items);
            // a(t,e) → term t selects no literal falsified by e.
            for (0..k) |t| {
                for (0..2 * num_features) |j| {
                    if (falsifies(e.features, @intCast(j))) {
                        try out.addClause(&.{
                            aVar(num_features, k, @intCast(t), pi).not(),
                            pVar(num_features, @intCast(t), @intCast(j)).not(),
                        });
                    }
                }
            }
            pi += 1;
        } else {
            // Every term selects at least one literal falsified by e.
            for (0..k) |t| {
                buf.clearRetainingCapacity();
                for (0..2 * num_features) |j| {
                    if (falsifies(e.features, @intCast(j))) {
                        try buf.append(allocator, pVar(num_features, @intCast(t), @intCast(j)));
                    }
                }
                try out.addClause(buf.items);
            }
        }
    }
    return out;
}

fn decode(
    allocator: std.mem.Allocator,
    num_features: u32,
    k: u32,
    model: []const lit_mod.Value,
) ![][]TermLit {
    var terms: std.ArrayList([]TermLit) = .empty;
    errdefer {
        for (terms.items) |t| allocator.free(t);
        terms.deinit(allocator);
    }
    var lits: std.ArrayList(TermLit) = .empty;
    defer lits.deinit(allocator);

    for (0..k) |t| {
        lits.clearRetainingCapacity();
        var dead = false;
        for (0..num_features) |f| {
            const pos = model[t * 2 * num_features + 2 * f] == .true_;
            const neg = model[t * 2 * num_features + 2 * f + 1] == .true_;
            if (pos and neg) {
                dead = true; // term ≡ false; drop (semantically inert in a DNF)
                break;
            }
            if (pos) try lits.append(allocator, .{ .feature = @intCast(f), .negated = false });
            if (neg) try lits.append(allocator, .{ .feature = @intCast(f), .negated = true });
        }
        if (!dead) try terms.append(allocator, try allocator.dupe(TermLit, lits.items));
    }
    return terms.toOwnedSlice(allocator);
}

fn verify(r: *const Result, examples: []const Example) bool {
    for (examples) |e| {
        if (evaluate(r.terms, e.features) != e.label) return false;
    }
    return true;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn ex(features: []const bool, label: bool) Example {
    return .{ .features = features, .label = label };
}

test "induce: conjunction x0 ∧ x1 at k=1" {
    const examples = [_]Example{
        ex(&.{ true, true }, true),
        ex(&.{ true, false }, false),
        ex(&.{ false, true }, false),
        ex(&.{ false, false }, false),
    };
    var r = try induceDnf(testing.allocator, 2, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expect(r.minimal);
    try testing.expectEqual(@as(u32, 1), r.k_used);
}

test "induce: disjunction x0 ∨ x1 at k≤2, still verified" {
    const examples = [_]Example{
        ex(&.{ true, true }, true),
        ex(&.{ true, false }, true),
        ex(&.{ false, true }, true),
        ex(&.{ false, false }, false),
    };
    var r = try induceDnf(testing.allocator, 2, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expect(r.minimal);
}

test "induce: xor needs exactly k=2" {
    const examples = [_]Example{
        ex(&.{ false, false }, false),
        ex(&.{ true, true }, false),
        ex(&.{ true, false }, true),
        ex(&.{ false, true }, true),
    };
    var r = try induceDnf(testing.allocator, 2, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expect(r.minimal);
    try testing.expectEqual(@as(u32, 2), r.k_used);
}

test "induce: 3-var parity needs k=4" {
    var feats: [8][3]bool = undefined;
    var examples: [8]Example = undefined;
    for (0..8) |i| {
        var ones: u32 = 0;
        for (0..3) |f| {
            feats[i][f] = (i >> @intCast(f)) & 1 == 1;
            if (feats[i][f]) ones += 1;
        }
        examples[i] = ex(&feats[i], ones % 2 == 1);
    }
    var r = try induceDnf(testing.allocator, 3, &examples, .{ .max_k = 5 });
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expect(r.minimal);
    try testing.expectEqual(@as(u32, 4), r.k_used);
}

test "induce: contradictory labels → no hypothesis" {
    const examples = [_]Example{
        ex(&.{ true, false }, true),
        ex(&.{ true, false }, false),
    };
    var r = try induceDnf(testing.allocator, 2, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .no_hypothesis);
}

test "induce: all negative → empty DNF (false)" {
    const examples = [_]Example{
        ex(&.{true}, false),
        ex(&.{false}, false),
    };
    var r = try induceDnf(testing.allocator, 1, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expectEqual(@as(usize, 0), r.terms.len);
}

test "induce: all positive → tautological hypothesis" {
    const examples = [_]Example{
        ex(&.{true}, true),
        ex(&.{false}, true),
    };
    var r = try induceDnf(testing.allocator, 1, &examples, .{});
    defer r.deinit();
    try testing.expect(r.status == .learned);
    try testing.expect(r.verified);
    try testing.expectEqual(@as(u32, 1), r.k_used);
}

test "peircean triad: abduce → induce → deduce" {
    const abduction = @import("abduction.zig");
    const lp = Lit.positive;
    const ln = Lit.negative;
    const v = Var.fromIndex;

    // Background: faultA → s1, faultB → s1, faultB → s2 (0=fA, 1=fB, 2=s1, 3=s2).
    var b = Cnf.init(testing.allocator);
    defer b.deinit();
    try b.addClause(&.{ ln(v(0)), lp(v(2)) });
    try b.addClause(&.{ ln(v(1)), lp(v(2)) });
    try b.addClause(&.{ ln(v(1)), lp(v(3)) });

    // Abduction: observing s1 ∧ s2, the unique minimal cause is faultB.
    var ar = try abduction.abduce(
        testing.allocator,
        &b,
        &.{ lp(v(2)), lp(v(3)) },
        &.{ lp(v(0)), lp(v(1)) },
        .{},
    );
    defer ar.deinit();
    try testing.expectEqual(@as(usize, 1), ar.explanations.items.len);
    try testing.expect(ar.explanations.items[0][0] == lp(v(1)));

    // Induction: compress observed (s1,s2) ↦ faultB episodes into a rule.
    const examples = [_]Example{
        ex(&.{ true, true }, true), // both symptoms → faultB episodes
        ex(&.{ true, false }, false), // s1 alone had another cause
        ex(&.{ false, false }, false),
    };
    var ir = try induceDnf(testing.allocator, 2, &examples, .{});
    defer ir.deinit();
    try testing.expect(ir.status == .learned);
    try testing.expect(ir.verified);
    try testing.expectEqual(@as(u32, 1), ir.k_used);

    // Deduction: certify the abduced cause against the background theory.
    try testing.expect(try abduction.verifyExplanation(
        testing.allocator,
        &b,
        &.{ lp(v(2)), lp(v(3)) },
        ar.explanations.items[0],
    ));
}
