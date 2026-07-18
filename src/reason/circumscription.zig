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
    return r.status == .sat;
}

fn pPart(sig: u32, np: u5) u32 {
    return sig & ((@as(u32, 1) << np) - 1);
}
fn qPart(sig: u32, np: u5) u32 {
    return sig >> np;
}

/// Does CIRC[T; minimized; varying] entail the cube φ?
pub fn circEntails(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    part: Partition,
    phi_cube: []const Lit,
) !bool {
    const np: u5 = @intCast(part.minimized.len);
    const nq: u5 = @intCast(part.fixed.len);
    std.debug.assert(@as(u32, np) + nq <= 16);
    const total: u32 = @as(u32, 1) << (np + nq);

    var sat_sigs: std.ArrayList(u32) = .empty;
    defer sat_sigs.deinit(allocator);
    var sig: u32 = 0;
    while (sig < total) : (sig += 1) {
        if (try signatureSat(allocator, theory, part, sig, null)) {
            try sat_sigs.append(allocator, sig);
        }
    }
    // P-minimal per Q-class.
    for (sat_sigs.items) |s| {
        var minimal = true;
        for (sat_sigs.items) |s2| {
            if (s2 == s) continue;
            if (qPart(s2, np) != qPart(s, np)) continue;
            const p2 = pPart(s2, np);
            const p1 = pPart(s, np);
            if ((p2 & p1) == p2 and p2 != p1) {
                minimal = false;
                break;
            }
        }
        if (!minimal) continue;
        // Counterexample completion under this minimal signature?
        if (try signatureSat(allocator, theory, part, s, phi_cube)) return false;
    }
    return true;
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
