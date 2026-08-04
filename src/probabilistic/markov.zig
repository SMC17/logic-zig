//! Markov logic networks — weighted first-order / propositional formulas.
//!
//! A MLN is a set of (weight, formula) pairs. Under a finite domain the
//! groundings induce a distribution:
//!   P(X=x) ∝ exp( Σ_i w_i · n_i(x) )
//! where n_i(x) is the number of true groundings of formula i in world x.
//!
//! Fragment: propositional MLN (already-ground formulas), world score,
//! normalized probability over an explicit enumeration of 2^n worlds (n≤12).
//! Not lifted inference / MC-SAT / MaxWalkSAT industrial stack.

const std = @import("std");
const prob = @import("prob.zig");

pub const WeightedFormula = struct {
    weight: f64,
    /// Propositional formula over atoms 0..n-1.
    formula: *prob.Formula,
};

pub const MLN = struct {
    formulas: []const WeightedFormula,
    n_atoms: u32,
};

/// Score of a world given as a bitset (bit i = atom i true).
pub fn worldScore(mln: *const MLN, world: u32) f64 {
    var score: f64 = 0;
    // Build assignment array
    var assign_buf: [12]prob.Prob = undefined;
    const n = mln.n_atoms;
    if (n > 12) return 0;
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        assign_buf[i] = if ((world & (@as(u32, 1) << @intCast(i))) != 0) 1.0 else 0.0;
    }
    for (mln.formulas) |wf| {
        const val = prob.evalIndep(wf.formula, assign_buf[0..n]);
        // formula true → contribute weight (soft: weight * truth degree)
        score += wf.weight * val;
    }
    return score;
}

pub fn worldProb(mln: *const MLN, world: u32) f64 {
    const n = mln.n_atoms;
    if (n > 12) return 0;
    const full: u32 = if (n == 0) 0 else (@as(u32, 1) << @intCast(n)) - 1;
    var z: f64 = 0;
    var w: u32 = 0;
    while (w <= full) : (w += 1) {
        z += @exp(worldScore(mln, w));
    }
    if (z == 0) return 0;
    return @exp(worldScore(mln, world)) / z;
}

/// Marginal P(atom i = true).
pub fn marginal(mln: *const MLN, atom: u32) f64 {
    const n = mln.n_atoms;
    if (n > 12 or atom >= n) return 0;
    const full: u32 = if (n == 0) 0 else (@as(u32, 1) << @intCast(n)) - 1;
    var z: f64 = 0;
    var mass: f64 = 0;
    var w: u32 = 0;
    while (w <= full) : (w += 1) {
        const p = @exp(worldScore(mln, w));
        z += p;
        if ((w & (@as(u32, 1) << @intCast(atom))) != 0) mass += p;
    }
    if (z == 0) return 0;
    return mass / z;
}

test "hard weight forces formula" {
    var arena = prob.Arena.init(std.testing.allocator);
    defer arena.deinit();
    // One atom a. Formula a with weight 10 → P(a) high.
    const a = try arena.f(.{ .atom = 0 });
    const mln = MLN{
        .formulas = &[_]WeightedFormula{.{ .weight = 10, .formula = a }},
        .n_atoms = 1,
    };
    const p_true = worldProb(&mln, 1);
    const p_false = worldProb(&mln, 0);
    try std.testing.expect(p_true > p_false);
    try std.testing.expect(p_true + p_false > 0.99);
}

test "marginal of unconstrained atom is half" {
    const mln = MLN{ .formulas = &[_]WeightedFormula{}, .n_atoms = 1 };
    const m = marginal(&mln, 0);
    try std.testing.expect(@abs(m - 0.5) < 1e-9);
}

test "soft conjunction weight" {
    var arena = prob.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = 0 });
    const b = try arena.f(.{ .atom = 1 });
    const conj = try arena.f(.{ .and_ = .{ .l = a, .r = b } });
    const mln = MLN{
        .formulas = &[_]WeightedFormula{.{ .weight = 5, .formula = conj }},
        .n_atoms = 2,
    };
    // World 0b11 should be most probable
    const p3 = worldProb(&mln, 0b11);
    const p0 = worldProb(&mln, 0b00);
    try std.testing.expect(p3 > p0);
}
