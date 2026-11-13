//! Bayesian / statistical induction — degrees of belief over hypotheses.
//!
//! Complements `reason/induction.zig` (exact SAT synthesis): here induction is
//! probabilistic. Two engines:
//!
//! 1. **Rule of succession** — Laplace's enumerative induction: after s
//!    successes in n trials, P(next success) = (s+α)/(n+α+β) with a Beta
//!    prior (α=β=1 gives the classic (s+1)/(n+2)).
//!
//! 2. **Exact posterior over the conjunction class** — hypotheses are
//!    conjunctions over boolean features (each feature: ignored, required
//!    true, or required false; 3^n hypotheses). Prior favors simplicity
//!    (Occam: P(h) ∝ θ^size). Likelihood is ε-noise: each label agrees with
//!    h(x) with probability 1−ε. Posterior is computed exactly (log-space),
//!    giving the MAP hypothesis and predictive probabilities by full Bayesian
//!    model averaging — Carnapian inductive logic on a finite language.
//!
//! Honest scope: finite propositional hypothesis class, exact enumeration
//! (n ≤ ~12 features). Not a graphical-model or MCMC engine.

const std = @import("std");

/// Laplace rule of succession with a Beta(α,β) prior.
pub fn ruleOfSuccession(successes: u64, trials: u64, alpha: f64, beta: f64) f64 {
    std.debug.assert(successes <= trials);
    const s: f64 = @floatFromInt(successes);
    const n: f64 = @floatFromInt(trials);
    return (s + alpha) / (n + alpha + beta);
}

/// Classic (s+1)/(n+2).
pub fn laplace(successes: u64, trials: u64) f64 {
    return ruleOfSuccession(successes, trials, 1.0, 1.0);
}

pub const Example = struct {
    features: []const bool,
    label: bool,
};

/// A conjunction hypothesis in base-3 digits: 0 = ignore feature,
/// 1 = require true, 2 = require false. Code 0 = empty conjunction (⊤).
pub const Hypothesis = struct {
    code: u64,
    num_features: u32,

    pub fn matches(self: Hypothesis, features: []const bool) bool {
        var c = self.code;
        for (0..self.num_features) |f| {
            const d = c % 3;
            c /= 3;
            if (d == 1 and !features[f]) return false;
            if (d == 2 and features[f]) return false;
        }
        return true;
    }

    pub fn size(self: Hypothesis) u32 {
        var c = self.code;
        var k: u32 = 0;
        for (0..self.num_features) |_| {
            if (c % 3 != 0) k += 1;
            c /= 3;
        }
        return k;
    }
};

pub const Options = struct {
    /// Label noise: P(observed label ≠ h(x)). Must be in [0, 0.5).
    noise: f64 = 0.01,
    /// Occam prior: P(h) ∝ simplicity_theta^size(h). In (0, 1].
    simplicity_theta: f64 = 0.5,
};

pub const Posterior = struct {
    allocator: std.mem.Allocator,
    num_features: u32,
    opts: Options,
    /// Log posterior (normalized) per hypothesis code.
    log_post: []f64,
    map: Hypothesis,

    pub fn deinit(self: *Posterior) void {
        self.allocator.free(self.log_post);
        self.* = undefined;
    }

    /// Posterior probability of one hypothesis.
    pub fn prob(self: *const Posterior, code: u64) f64 {
        return @exp(self.log_post[@intCast(code)]);
    }

    /// Predictive P(label = true | x, data) by full model averaging.
    pub fn predict(self: *const Posterior, features: []const bool) f64 {
        const eps = self.opts.noise;
        var p: f64 = 0;
        for (self.log_post, 0..) |lp_, code| {
            const h = Hypothesis{ .code = @intCast(code), .num_features = self.num_features };
            const p_true: f64 = if (h.matches(features)) 1.0 - eps else eps;
            p += @exp(lp_) * p_true;
        }
        return p;
    }
};

fn pow3(n: u32) u64 {
    var r: u64 = 1;
    for (0..n) |_| r *= 3;
    return r;
}

/// Exact Bayesian posterior over all conjunctions of the feature literals.
pub fn posterior(
    allocator: std.mem.Allocator,
    num_features: u32,
    examples: []const Example,
    opts: Options,
) !Posterior {
    std.debug.assert(opts.noise >= 0 and opts.noise < 0.5);
    std.debug.assert(opts.simplicity_theta > 0 and opts.simplicity_theta <= 1);
    for (examples) |e| std.debug.assert(e.features.len == num_features);
    const total = pow3(num_features);

    const log_post = try allocator.alloc(f64, @intCast(total));
    errdefer allocator.free(log_post);

    const log_theta = @log(opts.simplicity_theta);
    // ε=0 exactly: consistent hypotheses get log-lik 0, inconsistent −∞.
    const log_agree: f64 = @log(1.0 - opts.noise);
    const log_disagree: f64 = if (opts.noise == 0) -std.math.inf(f64) else @log(opts.noise);

    var best_code: u64 = 0;
    var best_lp = -std.math.inf(f64);
    for (0..@as(usize, @intCast(total))) |code| {
        const h = Hypothesis{ .code = @intCast(code), .num_features = num_features };
        var lp_: f64 = @as(f64, @floatFromInt(h.size())) * log_theta;
        for (examples) |e| {
            const agrees = h.matches(e.features) == e.label;
            lp_ += if (agrees) log_agree else log_disagree;
        }
        log_post[code] = lp_;
        // Tie-break toward simpler hypotheses (lower size, then lower code).
        if (lp_ > best_lp) {
            best_lp = lp_;
            best_code = @intCast(code);
        }
    }
    // Normalize: log-sum-exp.
    var sum: f64 = 0;
    for (log_post) |lp_| {
        if (lp_ != -std.math.inf(f64)) sum += @exp(lp_ - best_lp);
    }
    const log_z = best_lp + @log(sum);
    for (log_post) |*lp_| lp_.* -= log_z;

    return .{
        .allocator = allocator,
        .num_features = num_features,
        .opts = opts,
        .log_post = log_post,
        .map = .{ .code = best_code, .num_features = num_features },
    };
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn ex(features: []const bool, label: bool) Example {
    return .{ .features = features, .label = label };
}

test "bayes: rule of succession matches closed form" {
    try testing.expectApproxEqAbs(@as(f64, 0.5), laplace(0, 0), 1e-12);
    try testing.expectApproxEqAbs(@as(f64, 2.0 / 3.0), laplace(1, 1), 1e-12);
    try testing.expectApproxEqAbs(@as(f64, 6.0 / 12.0), laplace(5, 10), 1e-12);
    try testing.expectApproxEqAbs(@as(f64, 11.0 / 12.0), laplace(10, 10), 1e-12);
    // General Beta prior.
    try testing.expectApproxEqAbs(@as(f64, (3.0 + 2.0) / (4.0 + 5.0)), ruleOfSuccession(3, 4, 2.0, 3.0), 1e-12);
}

test "bayes: MAP recovers the target conjunction on noise-free separable data" {
    // Target: x0 ∧ ¬x1 over 3 features; all 8 rows labeled.
    var feats: [8][3]bool = undefined;
    var examples: [8]Example = undefined;
    for (0..8) |i| {
        for (0..3) |f| feats[i][f] = (i >> @intCast(f)) & 1 == 1;
        examples[i] = ex(&feats[i], feats[i][0] and !feats[i][1]);
    }
    var post = try posterior(testing.allocator, 3, &examples, .{ .noise = 0.001 });
    defer post.deinit();
    // MAP must classify every row exactly like the target.
    for (examples) |e| {
        try testing.expectEqual(e.label, post.map.matches(e.features));
    }
    // And be the target syntactically: requires x0 true, x1 false, ignores x2.
    try testing.expectEqual(@as(u32, 2), post.map.size());
    try testing.expect(post.map.matches(&.{ true, false, true }));
    try testing.expect(!post.map.matches(&.{ false, false, false }));
    try testing.expect(!post.map.matches(&.{ true, true, false }));
}

test "bayes: zero noise gives exact cut between consistent and impossible" {
    const examples = [_]Example{
        ex(&.{ true, true }, true),
        ex(&.{ false, true }, false),
    };
    var post = try posterior(testing.allocator, 2, &examples, .{ .noise = 0.0 });
    defer post.deinit();
    // Any hypothesis inconsistent with the data has posterior exactly 0.
    // ⊤ (code 0) matches everything → labels row2 true → inconsistent.
    try testing.expectEqual(@as(f64, 0), post.prob(0));
    // Posterior sums to 1 over the rest.
    var sum: f64 = 0;
    for (0..post.log_post.len) |c| sum += post.prob(@intCast(c));
    try testing.expectApproxEqAbs(@as(f64, 1.0), sum, 1e-9);
}

test "bayes: predictive converges toward certainty with accumulating evidence" {
    // Repeated (x0=true → label true), (x0=false → label false).
    var examples: std.ArrayList(Example) = .empty;
    defer examples.deinit(testing.allocator);
    const t = [_]bool{true};
    const f = [_]bool{false};
    var last: f64 = 0;
    var reps: u32 = 1;
    while (reps <= 8) : (reps *= 2) {
        examples.clearRetainingCapacity();
        for (0..reps) |_| {
            try examples.append(testing.allocator, ex(&t, true));
            try examples.append(testing.allocator, ex(&f, false));
        }
        var post = try posterior(testing.allocator, 1, examples.items, .{ .noise = 0.05 });
        defer post.deinit();
        const p = post.predict(&t);
        try testing.expect(p > 0.5);
        try testing.expect(p >= last); // monotone approach with doubling data
        last = p;
    }
    try testing.expect(last > 0.9);
}

test "bayes: Occam prior picks the simpler of two equally consistent hypotheses" {
    // Data: only rows where x0=x1; label = x0. Both "x0" and "x0∧x1" fit;
    // prior must prefer the singleton conjunction as MAP.
    const examples = [_]Example{
        ex(&.{ true, true }, true),
        ex(&.{ false, false }, false),
    };
    var post = try posterior(testing.allocator, 2, &examples, .{ .noise = 0.0 });
    defer post.deinit();
    try testing.expectEqual(@as(u32, 1), post.map.size());
    try testing.expect(post.map.matches(&.{ true, false }));
}
