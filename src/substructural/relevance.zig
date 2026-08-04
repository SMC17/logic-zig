//! Relevance logic R — variable-sharing and fusion spine.
//!
//! Classical material implication validates A → (B → A) (positive paradox).
//! Relevance logics require that antecedent and consequent share a propositional
//! variable (variable-sharing property) and treat implication as a resource-
//! sensitive residual of fusion (∘).
//!
//! Fragment:
//!   - Formula AST with relevant implication (→ᵣ) and fusion (∘)
//!   - Variable-sharing check on implications
//!   - Rejection of positive paradox instances
//! Not a full Routley-Meyer semantics or proof theory for R.

const std = @import("std");

pub const Formula = union(enum) {
    atom: []const u8,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    /// Relevant implication
    impl: struct { l: *Formula, r: *Formula },
    /// Fusion (intensional conjunction)
    fusion: struct { l: *Formula, r: *Formula },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*Formula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }
    pub fn f(self: *Arena, v: Formula) !*Formula {
        const p = try self.allocator.create(Formula);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

fn collectAtoms(phi: *const Formula, set: *std.StringHashMap(void)) !void {
    switch (phi.*) {
        .atom => |a| try set.put(a, {}),
        .not => |n| try collectAtoms(n, set),
        .and_ => |a| {
            try collectAtoms(a.l, set);
            try collectAtoms(a.r, set);
        },
        .or_ => |a| {
            try collectAtoms(a.l, set);
            try collectAtoms(a.r, set);
        },
        .impl => |a| {
            try collectAtoms(a.l, set);
            try collectAtoms(a.r, set);
        },
        .fusion => |a| {
            try collectAtoms(a.l, set);
            try collectAtoms(a.r, set);
        },
    }
}

/// Variable-sharing: vars(A) ∩ vars(B) ≠ ∅ for A →ᵣ B.
pub fn sharesVariable(allocator: std.mem.Allocator, ant: *const Formula, cons: *const Formula) !bool {
    var left = std.StringHashMap(void).init(allocator);
    defer left.deinit();
    var right = std.StringHashMap(void).init(allocator);
    defer right.deinit();
    try collectAtoms(ant, &left);
    try collectAtoms(cons, &right);
    var it = left.keyIterator();
    while (it.next()) |k| {
        if (right.contains(k.*)) return true;
    }
    return false;
}

/// Does this implication formula satisfy variable-sharing?
pub fn relevantImplication(allocator: std.mem.Allocator, phi: *const Formula) !bool {
    return switch (phi.*) {
        .impl => |i| sharesVariable(allocator, i.l, i.r),
        else => false,
    };
}

/// Positive paradox A → (B → A) fails variable-sharing on the outer implication
/// when B is a fresh atom.
pub fn isPositiveParadox(allocator: std.mem.Allocator, phi: *const Formula) !bool {
    // Pattern: A → (B → A) with vars(B) ∩ vars(A) = ∅ on the inner, and outer
    // shares via A — actually outer shares. The paradox is accepted classically
    // but relevance rejects theorems where some sub-implication fails sharing.
    // We flag any implication subformula that fails sharing.
    return switch (phi.*) {
        .impl => |i| blk: {
            if (!try sharesVariable(allocator, i.l, i.r)) break :blk true;
            break :blk try isPositiveParadox(allocator, i.l) or try isPositiveParadox(allocator, i.r);
        },
        .not => |n| try isPositiveParadox(allocator, n),
        .and_ => |a| try isPositiveParadox(allocator, a.l) or try isPositiveParadox(allocator, a.r),
        .or_ => |a| try isPositiveParadox(allocator, a.l) or try isPositiveParadox(allocator, a.r),
        .fusion => |a| try isPositiveParadox(allocator, a.l) or try isPositiveParadox(allocator, a.r),
        .atom => false,
    };
}

test "shares variable on related atoms" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = "A" });
    const b = try arena.f(.{ .atom = "A" }); // same
    try std.testing.expect(try sharesVariable(std.testing.allocator, a, b));
}

test "no share on disjoint atoms" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = "A" });
    const b = try arena.f(.{ .atom = "B" });
    try std.testing.expect(!try sharesVariable(std.testing.allocator, a, b));
}

test "positive paradox detected" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    // A → (B → A): outer shares A; inner B → A fails sharing
    const a = try arena.f(.{ .atom = "A" });
    const b = try arena.f(.{ .atom = "B" });
    const inner = try arena.f(.{ .impl = .{ .l = b, .r = a } });
    const outer = try arena.f(.{ .impl = .{ .l = a, .r = inner } });
    try std.testing.expect(try isPositiveParadox(std.testing.allocator, outer));
}

test "relevant A → A ok" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a1 = try arena.f(.{ .atom = "A" });
    const a2 = try arena.f(.{ .atom = "A" });
    const imp = try arena.f(.{ .impl = .{ .l = a1, .r = a2 } });
    try std.testing.expect(try relevantImplication(std.testing.allocator, imp));
    try std.testing.expect(!try isPositiveParadox(std.testing.allocator, imp));
}
