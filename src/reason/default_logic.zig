//! Reiter default logic (propositional, finite).
//!
//! A default theory is (W, D): hard knowledge W (CNF) and defaults
//!
//!     prereq : just₁, …, justₖ
//!     ─────────────────────────
//!           consequent
//!
//! with prereq/justifications/consequent cubes of literals. An extension is
//! characterized by its generating set GD ⊆ D, checked with the standard
//! finite conditions, all via the SAT oracle:
//!
//!   groundedness — GD is reachable by iterated application: starting from W,
//!     repeatedly apply defaults in GD whose prerequisite is entailed;
//!     every member of GD must fire (no self-supporting circles);
//!   justification consistency — each justification of each applied default
//!     is consistent with the *final* extension E = Th(W ∪ cons(GD));
//!   stability — no default outside GD is applicable to E (prerequisite
//!     entailed and all justifications consistent).
//!
//! Extensions are enumerated over subsets of D (exponential; intended for
//! small default sets — the classic fixtures, agent policies, tests).
//! Canonical behaviors covered: Tweety (exception blocks the default),
//! Nixon diamond (two extensions), ( :p / ¬p ) (no extension), groundedness
//! (no self-justifying extensions), and W-inconsistent degeneracy.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const solver_mod = @import("../sat/solver.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Lit = lit_mod.Lit;

pub const Default = struct {
    /// Cube; empty = ⊤ (always applicable prerequisite).
    prereq: []const Lit = &.{},
    /// Cubes, each must be individually consistent with the extension.
    /// Empty list = no justification obligations (classical rule).
    justifications: []const []const Lit = &.{},
    /// Cube added when the default fires.
    consequent: []const Lit,
};

pub const Options = struct {
    /// Refuse enumeration beyond this many defaults (2^n subsets).
    max_defaults: u32 = 20,
};

pub const TheoryError = error{
    TooManyDefaults,
    InvalidDefaultLimit,
    GeneratingSetLengthMismatch,
};

pub const absolute_max_defaults: u32 = 20;

fn validateTheory(defaults: []const Default, opts: Options) TheoryError!void {
    if (opts.max_defaults > absolute_max_defaults) return error.InvalidDefaultLimit;
    if (defaults.len > opts.max_defaults) return error.TooManyDefaults;
}

pub const ExtensionsResult = struct {
    allocator: std.mem.Allocator,
    /// Each extension as its generating set (owned bool slice, parallel to D).
    generating: std.ArrayList([]bool) = .empty,

    pub fn deinit(self: *ExtensionsResult) void {
        for (self.generating.items) |g| self.allocator.free(g);
        self.generating.deinit(self.allocator);
        self.* = undefined;
    }
};

/// Theory = W ∪ consequents of selected defaults (as unit cubes).
fn buildTheory(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    selected: []const bool,
) !Cnf {
    var out = Cnf.init(allocator);
    errdefer out.deinit();
    out.ensureVars(w.num_vars);
    for (0..w.numClauses()) |ci| {
        try out.addClause(w.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    for (defaults, selected) |d, on| {
        for (d.prereq) |l| out.ensureVars(l.variable().index() + 1);
        for (d.justifications) |j| for (j) |l| out.ensureVars(l.variable().index() + 1);
        for (d.consequent) |l| out.ensureVars(l.variable().index() + 1);
        if (on) {
            for (d.consequent) |l| try out.addClause(&.{l});
        }
    }
    return out;
}

fn isSat(allocator: std.mem.Allocator, theory: *const Cnf, extra_units: []const Lit) !bool {
    var t = Cnf.init(allocator);
    defer t.deinit();
    t.ensureVars(theory.num_vars);
    for (0..theory.numClauses()) |ci| {
        try t.addClause(theory.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    for (extra_units) |l| {
        t.ensureVars(l.variable().index() + 1);
        try t.addClause(&.{l});
    }
    const r = try solver_mod.solveCnf(allocator, &t, .{});
    defer if (r.model) |m| allocator.free(m);
    return r.status == .sat;
}

/// theory ⊨ cube — every literal of the cube entailed.
fn entailsCube(allocator: std.mem.Allocator, theory: *const Cnf, cube: []const Lit) !bool {
    if (cube.len == 0) return true;
    var t = Cnf.init(allocator);
    defer t.deinit();
    t.ensureVars(theory.num_vars);
    for (0..theory.numClauses()) |ci| {
        try t.addClause(theory.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    var neg: std.ArrayList(Lit) = .empty;
    defer neg.deinit(allocator);
    for (cube) |l| {
        t.ensureVars(l.variable().index() + 1);
        try neg.append(allocator, l.not());
    }
    try t.addClause(neg.items);
    const r = try solver_mod.solveCnf(allocator, &t, .{});
    defer if (r.model) |m| allocator.free(m);
    return r.status == .unsat;
}

fn isExtension(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    gd: []const bool,
) !bool {
    const n = defaults.len;
    // Final candidate extension theory E = Th(W ∪ cons(GD)).
    var ext = try buildTheory(allocator, w, defaults, gd);
    defer ext.deinit();

    // Groundedness: iterated application from W must fire every GD member.
    {
        var fired = try allocator.alloc(bool, n);
        defer allocator.free(fired);
        @memset(fired, false);
        var stage = try buildTheory(allocator, w, defaults, fired);
        defer stage.deinit();
        var progress = true;
        while (progress) {
            progress = false;
            for (defaults, 0..) |d, i| {
                if (!gd[i] or fired[i]) continue;
                if (try entailsCube(allocator, &stage, d.prereq)) {
                    fired[i] = true;
                    for (d.consequent) |l| {
                        stage.ensureVars(l.variable().index() + 1);
                        try stage.addClause(&.{l});
                    }
                    progress = true;
                }
            }
        }
        for (0..n) |i| {
            if (gd[i] and !fired[i]) return false;
        }
    }
    // Justification consistency against the final extension.
    for (defaults, gd) |d, on| {
        if (!on) continue;
        for (d.justifications) |j| {
            if (!try isSat(allocator, &ext, j)) return false;
        }
    }
    // Stability: no outside default is applicable.
    for (defaults, 0..) |d, i| {
        if (gd[i]) continue;
        if (!try entailsCube(allocator, &ext, d.prereq)) continue;
        var all_consistent = true;
        for (d.justifications) |j| {
            if (!try isSat(allocator, &ext, j)) {
                all_consistent = false;
                break;
            }
        }
        if (all_consistent) return false; // applicable but unapplied
    }
    return true;
}

/// Enumerate all Reiter extensions by generating set.
pub fn extensions(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    opts: Options,
) !ExtensionsResult {
    try validateTheory(defaults, opts);
    var result = ExtensionsResult{ .allocator = allocator };
    errdefer result.deinit();

    const n: u5 = @intCast(defaults.len);
    const total: u32 = @as(u32, 1) << n;
    var gd = try allocator.alloc(bool, defaults.len);
    defer allocator.free(gd);
    var mask: u32 = 0;
    while (mask < total) : (mask += 1) {
        for (0..defaults.len) |i| gd[i] = (mask >> @intCast(i)) & 1 == 1;
        if (try isExtension(allocator, w, defaults, gd)) {
            try result.generating.append(allocator, try allocator.dupe(bool, gd));
        }
    }
    return result;
}

fn sameGeneratingSet(a: []const bool, b: []const bool) bool {
    return std.mem.eql(bool, a, b);
}

/// Verify exact extension evidence. Every claimed generating set must have the
/// right shape, be unique, and correspond exactly to one stable grounded Reiter
/// extension; every valid generating set must be present.
pub fn verifyExtensions(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    opts: Options,
    claimed: []const []bool,
) !bool {
    try validateTheory(defaults, opts);
    for (claimed, 0..) |gd, index| {
        if (gd.len != defaults.len) return false;
        for (claimed[index + 1 ..]) |other| {
            if (sameGeneratingSet(gd, other)) return false;
        }
    }
    const n: u5 = @intCast(defaults.len);
    const total: u32 = @as(u32, 1) << n;
    var gd = try allocator.alloc(bool, defaults.len);
    defer allocator.free(gd);
    var mask: u32 = 0;
    while (mask < total) : (mask += 1) {
        for (0..defaults.len) |i| gd[i] = (mask >> @intCast(i)) & 1 == 1;
        const expected = try isExtension(allocator, w, defaults, gd);
        var present = false;
        for (claimed) |candidate| {
            if (sameGeneratingSet(gd, candidate)) {
                present = true;
                break;
            }
        }
        if (present != expected) return false;
    }
    return true;
}

/// Does the extension generated by `gd` entail the query cube?
pub fn extensionEntails(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    gd: []const bool,
    query: []const Lit,
) !bool {
    if (gd.len != defaults.len) return error.GeneratingSetLengthMismatch;
    var ext = try buildTheory(allocator, w, defaults, gd);
    defer ext.deinit();
    return entailsCube(allocator, &ext, query);
}

pub const Consequence = enum { skeptical, credulous };

/// Skeptical: query holds in every extension. Credulous: in at least one.
/// A theory with no extensions yields skeptical=true vacuously (flagged off
/// here: returns false when there are no extensions, which is the useful
/// engineering answer; callers can inspect `extensions` directly).
pub fn entails(
    allocator: std.mem.Allocator,
    w: *const Cnf,
    defaults: []const Default,
    exts: *const ExtensionsResult,
    query: []const Lit,
    mode: Consequence,
) !bool {
    if (exts.generating.items.len == 0) return false;
    for (exts.generating.items) |gd| {
        const holds = try extensionEntails(allocator, w, defaults, gd, query);
        switch (mode) {
            .credulous => if (holds) return true,
            .skeptical => if (!holds) return false,
        }
    }
    return mode == .skeptical;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;
const Var = lit_mod.Var;

fn lp(v: u32) Lit {
    return Lit.positive(Var.fromIndex(v));
}
fn ln(v: u32) Lit {
    return Lit.negative(Var.fromIndex(v));
}

test "default: tweety — exception blocks the flying default" {
    // 0=penguin, 1=bird, 2=flies. W: penguin, penguin→bird, penguin→¬flies.
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    try w.addClause(&.{lp(0)});
    try w.addClause(&.{ ln(0), lp(1) });
    try w.addClause(&.{ ln(0), ln(2) });
    const d = [_]Default{
        .{ .prereq = &.{lp(1)}, .justifications = &.{&.{lp(2)}}, .consequent = &.{lp(2)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 1), exts.generating.items.len);
    try testing.expect(!exts.generating.items[0][0]); // default did not fire
    try testing.expect(try entails(testing.allocator, &w, &d, &exts, &.{ln(2)}, .skeptical));
}

test "default: tweety without the exception — bird flies" {
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    try w.addClause(&.{lp(1)}); // just a bird
    w.ensureVars(3);
    const d = [_]Default{
        .{ .prereq = &.{lp(1)}, .justifications = &.{&.{lp(2)}}, .consequent = &.{lp(2)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 1), exts.generating.items.len);
    try testing.expect(exts.generating.items[0][0]);
    try testing.expect(try entails(testing.allocator, &w, &d, &exts, &.{lp(2)}, .skeptical));
}

test "default: nixon diamond — exactly two extensions, skeptical silence" {
    // 0=quaker, 1=republican, 2=pacifist. W: quaker, republican.
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    try w.addClause(&.{lp(0)});
    try w.addClause(&.{lp(1)});
    const d = [_]Default{
        .{ .prereq = &.{lp(0)}, .justifications = &.{&.{lp(2)}}, .consequent = &.{lp(2)} },
        .{ .prereq = &.{lp(1)}, .justifications = &.{&.{ln(2)}}, .consequent = &.{ln(2)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 2), exts.generating.items.len);
    // Credulous both ways; skeptical neither.
    try testing.expect(try entails(testing.allocator, &w, &d, &exts, &.{lp(2)}, .credulous));
    try testing.expect(try entails(testing.allocator, &w, &d, &exts, &.{ln(2)}, .credulous));
    try testing.expect(!try entails(testing.allocator, &w, &d, &exts, &.{lp(2)}, .skeptical));
    try testing.expect(!try entails(testing.allocator, &w, &d, &exts, &.{ln(2)}, .skeptical));
}

test "default: ( :p / ¬p ) has no extension" {
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    w.ensureVars(1);
    const d = [_]Default{
        .{ .justifications = &.{&.{lp(0)}}, .consequent = &.{ln(0)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 0), exts.generating.items.len);
}

test "default: groundedness rejects self-supporting extension" {
    // d = (p : ⊤ / p): may not bootstrap itself.
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    w.ensureVars(1);
    const d = [_]Default{
        .{ .prereq = &.{lp(0)}, .consequent = &.{lp(0)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 1), exts.generating.items.len);
    try testing.expect(!exts.generating.items[0][0]);
}

test "default: chained normal defaults fire in sequence" {
    // W={a}; (a:b/b), (b:c/c) → unique extension containing c.
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    try w.addClause(&.{lp(0)});
    const d = [_]Default{
        .{ .prereq = &.{lp(0)}, .justifications = &.{&.{lp(1)}}, .consequent = &.{lp(1)} },
        .{ .prereq = &.{lp(1)}, .justifications = &.{&.{lp(2)}}, .consequent = &.{lp(2)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 1), exts.generating.items.len);
    try testing.expect(exts.generating.items[0][0] and exts.generating.items[0][1]);
    try testing.expect(try entails(testing.allocator, &w, &d, &exts, &.{lp(2)}, .skeptical));
}

test "default: inconsistent W → unique degenerate extension with nothing fired" {
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    try w.addClause(&.{lp(0)});
    try w.addClause(&.{ln(0)});
    const d = [_]Default{
        .{ .justifications = &.{&.{lp(1)}}, .consequent = &.{lp(1)} },
    };
    var exts = try extensions(testing.allocator, &w, &d, .{});
    defer exts.deinit();
    try testing.expectEqual(@as(usize, 1), exts.generating.items.len);
    try testing.expect(!exts.generating.items[0][0]);
}

test "default: exact extension evidence replays across a bounded theory universe" {
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    w.ensureVars(2);
    const universe = [_]Default{
        .{ .justifications = &.{&.{lp(0)}}, .consequent = &.{lp(0)} },
        .{ .justifications = &.{&.{ln(0)}}, .consequent = &.{ln(0)} },
        .{ .prereq = &.{lp(0)}, .justifications = &.{&.{lp(1)}}, .consequent = &.{lp(1)} },
        .{ .prereq = &.{lp(1)}, .consequent = &.{lp(0)} },
    };
    var defaults: std.ArrayList(Default) = .empty;
    defer defaults.deinit(testing.allocator);
    var theory: u32 = 0;
    while (theory < (@as(u32, 1) << universe.len)) : (theory += 1) {
        defaults.clearRetainingCapacity();
        for (universe, 0..) |default, index| {
            if ((theory >> @intCast(index)) & 1 == 1) try defaults.append(testing.allocator, default);
        }
        var exts = try extensions(testing.allocator, &w, defaults.items, .{});
        try testing.expect(try verifyExtensions(testing.allocator, &w, defaults.items, .{}, exts.generating.items));
        exts.deinit();
    }
}

test "default: malformed bounds and mutated extension evidence fail closed" {
    var w = Cnf.init(testing.allocator);
    defer w.deinit();
    w.ensureVars(1);
    const default = Default{ .justifications = &.{&.{lp(0)}}, .consequent = &.{lp(0)} };
    const too_many = [_]Default{default} ** 2;
    try testing.expectError(error.TooManyDefaults, extensions(testing.allocator, &w, &too_many, .{ .max_defaults = 1 }));
    try testing.expectError(error.InvalidDefaultLimit, extensions(testing.allocator, &w, &.{default}, .{ .max_defaults = 21 }));
    try testing.expectError(error.GeneratingSetLengthMismatch, extensionEntails(testing.allocator, &w, &.{default}, &.{}, &.{lp(0)}));

    var exts = try extensions(testing.allocator, &w, &.{default}, .{});
    defer exts.deinit();
    try testing.expect(try verifyExtensions(testing.allocator, &w, &.{default}, .{}, exts.generating.items));
    const removed = exts.generating.pop().?;
    defer testing.allocator.free(removed);
    try testing.expect(!(try verifyExtensions(testing.allocator, &w, &.{default}, .{}, exts.generating.items)));
}
