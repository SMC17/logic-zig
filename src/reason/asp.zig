//! Answer-set programming — stable models of propositional normal programs.
//!
//! Rules: `head ← pos₁,…,posₘ, not neg₁,…, not negₖ` (head absent = integrity
//! constraint). A candidate set M is a **stable model** (Gelfond–Lifschitz)
//! iff M equals the least model of the reduct P^M (drop rules whose negative
//! body intersects M; strip negative bodies from the rest) and no constraint
//! fires under M.
//!
//! Enumeration is exact guess-and-check over atom subsets (n ≤ 16 — canon
//! programs, agent policies; no claim of clingo-scale grounding/solving).
//! The reduct least-model check is the definitional certificate: every
//! returned model is verifiably the least model of its own reduct.

const std = @import("std");

pub const Rule = struct {
    /// Head atom; null = integrity constraint (⊥ head).
    head: ?u32,
    /// Positive body atoms.
    pos: []const u32 = &.{},
    /// Negated-as-failure body atoms.
    neg: []const u32 = &.{},
};

pub const Options = struct {
    max_atoms: u32 = 16,
};

pub const ProgramError = error{
    TooManyAtoms,
    InvalidAtomLimit,
    AtomOutOfRange,
};

/// The subset representation is a `u32`; the lower limit keeps exhaustive
/// enumeration within the explicitly supported exhibit contract.
pub const absolute_max_atoms: u32 = 20;

pub fn validateProgram(num_atoms: u32, rules: []const Rule, opts: Options) ProgramError!void {
    if (opts.max_atoms > absolute_max_atoms) return error.InvalidAtomLimit;
    if (num_atoms > opts.max_atoms) return error.TooManyAtoms;
    for (rules) |rule| {
        if (rule.head) |head| if (head >= num_atoms) return error.AtomOutOfRange;
        for (rule.pos) |atom| if (atom >= num_atoms) return error.AtomOutOfRange;
        for (rule.neg) |atom| if (atom >= num_atoms) return error.AtomOutOfRange;
    }
}

pub const Result = struct {
    allocator: std.mem.Allocator,
    /// Stable models as bitmasks over atom ids.
    models: std.ArrayList(u32) = .empty,

    pub fn deinit(self: *Result) void {
        self.models.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn contains(self: *const Result, m: u32) bool {
        for (self.models.items) |x| {
            if (x == m) return true;
        }
        return false;
    }
};

fn bit(a: u32) u32 {
    return @as(u32, 1) << @intCast(a);
}

/// Least model of the reduct P^M (definite program forward chaining),
/// or null when a constraint of the reduct fires under M.
pub fn reductLeastModel(rules: []const Rule, m: u32) ?u32 {
    // Constraint check first: body satisfied by M (pos ⊆ M, neg ∩ M = ∅) → ⊥.
    for (rules) |r| {
        if (r.head != null) continue;
        var fires = true;
        for (r.pos) |p| {
            if (m & bit(p) == 0) {
                fires = false;
                break;
            }
        }
        if (fires) for (r.neg) |ng| {
            if (m & bit(ng) != 0) {
                fires = false;
                break;
            }
        };
        if (fires) return null;
    }
    // Forward chaining on the reduct of head rules.
    var lm: u32 = 0;
    var progress = true;
    while (progress) {
        progress = false;
        for (rules) |r| {
            const h = r.head orelse continue;
            if (lm & bit(h) != 0) continue;
            // Reduct keeps the rule iff neg ∩ M = ∅.
            var kept = true;
            for (r.neg) |ng| {
                if (m & bit(ng) != 0) {
                    kept = false;
                    break;
                }
            }
            if (!kept) continue;
            var body_ok = true;
            for (r.pos) |p| {
                if (lm & bit(p) == 0) {
                    body_ok = false;
                    break;
                }
            }
            if (body_ok) {
                lm |= bit(h);
                progress = true;
            }
        }
    }
    return lm;
}

pub fn stableModels(
    allocator: std.mem.Allocator,
    num_atoms: u32,
    rules: []const Rule,
    opts: Options,
) !Result {
    try validateProgram(num_atoms, rules, opts);
    var result = Result{ .allocator = allocator };
    errdefer result.deinit();
    const total: u32 = @as(u32, 1) << @intCast(num_atoms);
    var m: u32 = 0;
    while (m < total) : (m += 1) {
        if (reductLeastModel(rules, m)) |lm| {
            if (lm == m) try result.models.append(allocator, m);
        }
    }
    return result;
}

/// Check one candidate directly against the Gelfond-Lifschitz definition.
pub fn isStableModel(num_atoms: u32, rules: []const Rule, candidate: u32, opts: Options) !bool {
    try validateProgram(num_atoms, rules, opts);
    const total: u32 = @as(u32, 1) << @intCast(num_atoms);
    if (candidate >= total) return false;
    const least = reductLeastModel(rules, candidate) orelse return false;
    return least == candidate;
}

/// Verify exact stable-model evidence: every claimed model is stable, and every
/// stable model in the finite carrier is present exactly once. This also makes
/// an empty list replayable evidence that the program has no stable model.
pub fn verifyModels(num_atoms: u32, rules: []const Rule, opts: Options, claimed: []const u32) !bool {
    try validateProgram(num_atoms, rules, opts);
    const total: u32 = @as(u32, 1) << @intCast(num_atoms);
    for (claimed, 0..) |model, index| {
        if (model >= total) return false;
        for (claimed[index + 1 ..]) |other| {
            if (model == other) return false;
        }
    }
    var candidate: u32 = 0;
    while (candidate < total) : (candidate += 1) {
        const least = reductLeastModel(rules, candidate);
        const expected = least != null and least.? == candidate;
        var present = false;
        for (claimed) |model| {
            if (model == candidate) {
                present = true;
                break;
            }
        }
        if (present != expected) return false;
    }
    return true;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "asp: even negative loop — two stable models" {
    // p ← not q.  q ← not p.
    const rules = [_]Rule{
        .{ .head = 0, .neg = &.{1} },
        .{ .head = 1, .neg = &.{0} },
    };
    var r = try stableModels(testing.allocator, 2, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 2), r.models.items.len);
    try testing.expect(r.contains(bit(0)) and r.contains(bit(1)));
}

test "asp: odd negative loop — no stable model" {
    // p ← not p.
    const rules = [_]Rule{
        .{ .head = 0, .neg = &.{0} },
    };
    var r = try stableModels(testing.allocator, 1, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 0), r.models.items.len);
}

test "asp: constraint prunes one answer set" {
    // p ← not q.  q ← not p.  ⊥ ← p.
    const rules = [_]Rule{
        .{ .head = 0, .neg = &.{1} },
        .{ .head = 1, .neg = &.{0} },
        .{ .head = null, .pos = &.{0} },
    };
    var r = try stableModels(testing.allocator, 2, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 1), r.models.items.len);
    try testing.expect(r.contains(bit(1)));
}

test "asp: stratified program — unique model, negation as failure" {
    // a.  b ← a.  c ← b, not d.   (d underivable)
    const rules = [_]Rule{
        .{ .head = 0 },
        .{ .head = 1, .pos = &.{0} },
        .{ .head = 2, .pos = &.{1}, .neg = &.{3} },
    };
    var r = try stableModels(testing.allocator, 4, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 1), r.models.items.len);
    try testing.expectEqual(bit(0) | bit(1) | bit(2), r.models.items[0]);
}

test "asp: positive loop is unfounded — supported-but-unstable model rejected" {
    // p ← q.  q ← p.  {p,q} is a supported model but NOT stable.
    const rules = [_]Rule{
        .{ .head = 0, .pos = &.{1} },
        .{ .head = 1, .pos = &.{0} },
    };
    var r = try stableModels(testing.allocator, 2, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 1), r.models.items.len);
    try testing.expectEqual(@as(u32, 0), r.models.items[0]);
    // Certificate: {p,q} is not the least model of its reduct.
    try testing.expect(reductLeastModel(&rules, bit(0) | bit(1)).? != (bit(0) | bit(1)));
}

test "asp: choice via even loop + dependent fact" {
    // p ← not q.  q ← not p.  r ← p.
    const rules = [_]Rule{
        .{ .head = 0, .neg = &.{1} },
        .{ .head = 1, .neg = &.{0} },
        .{ .head = 2, .pos = &.{0} },
    };
    var r = try stableModels(testing.allocator, 3, &rules, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 2), r.models.items.len);
    try testing.expect(r.contains(bit(0) | bit(2)) and r.contains(bit(1)));
}

test "asp: exact evidence replays across a bounded program universe" {
    // Every subset of this rule universe is a distinct two-atom normal program.
    const universe = [_]Rule{
        .{ .head = 0 },
        .{ .head = 1 },
        .{ .head = 0, .pos = &.{1} },
        .{ .head = 1, .pos = &.{0} },
        .{ .head = 0, .neg = &.{1} },
        .{ .head = 1, .neg = &.{0} },
        .{ .head = null, .pos = &.{0} },
        .{ .head = null, .neg = &.{1} },
    };
    var rules: std.ArrayList(Rule) = .empty;
    defer rules.deinit(testing.allocator);
    var program: u32 = 0;
    while (program < (@as(u32, 1) << universe.len)) : (program += 1) {
        rules.clearRetainingCapacity();
        for (universe, 0..) |rule, index| {
            if ((program >> @intCast(index)) & 1 == 1) try rules.append(testing.allocator, rule);
        }
        var result = try stableModels(testing.allocator, 2, rules.items, .{});
        try testing.expect(try verifyModels(2, rules.items, .{}, result.models.items));
        result.deinit();
    }
}

test "asp: malformed programs and mutated exact evidence fail closed" {
    const malformed = [_]Rule{.{ .head = 2 }};
    try testing.expectError(error.AtomOutOfRange, stableModels(testing.allocator, 2, &malformed, .{}));
    try testing.expectError(error.TooManyAtoms, stableModels(testing.allocator, 17, &.{}, .{}));
    try testing.expectError(error.InvalidAtomLimit, stableModels(testing.allocator, 2, &.{}, .{ .max_atoms = 21 }));

    const rules = [_]Rule{
        .{ .head = 0, .neg = &.{1} },
        .{ .head = 1, .neg = &.{0} },
    };
    var result = try stableModels(testing.allocator, 2, &rules, .{});
    defer result.deinit();
    try testing.expect(try verifyModels(2, &rules, .{}, result.models.items));
    _ = result.models.pop();
    try testing.expect(!(try verifyModels(2, &rules, .{}, result.models.items)));
    try result.models.append(testing.allocator, result.models.items[0]);
    try testing.expect(!(try verifyModels(2, &rules, .{}, result.models.items)));
}
