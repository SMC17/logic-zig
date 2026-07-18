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
    std.debug.assert(num_atoms <= opts.max_atoms);
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
