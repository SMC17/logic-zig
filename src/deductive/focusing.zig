//! Focusing proof search — Andreoli-style synchronous/async phases.
//!
//! Classical/intuitionistic propositional fragment with polarities:
//!   Positive (sync):  ⊗, ⊕, 1, 0, atoms⁺
//!   Negative (async): ⊸, &, ⊤, atoms⁻
//!
//! Inversion phase eagerly applies all invertible (async) rules.
//! Focus phase picks one positive formula and decomposes it fully.
//!
//! Fragment: polarity assignment + inversion/focus drivers over a linear-ish
//! context of polarized formulas. Not a full focused sequent calculus with
//! higher-order unification.

const std = @import("std");

pub const Polarity = enum { pos, neg };

pub const Formula = union(enum) {
    atom: struct { name: []const u8, pol: Polarity },
    tensor: struct { l: *Formula, r: *Formula }, // ⊗ positive
    plus: struct { l: *Formula, r: *Formula }, // ⊕ positive
    with: struct { l: *Formula, r: *Formula }, // & negative
    lolli: struct { l: *Formula, r: *Formula }, // ⊸ negative
    one, // 1 positive
    top, // ⊤ negative
    zero, // 0 positive
};

pub fn polarity(phi: *const Formula) Polarity {
    return switch (phi.*) {
        .atom => |a| a.pol,
        .tensor, .plus, .one, .zero => .pos,
        .with, .lolli, .top => .neg,
    };
}

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

pub const Phase = enum { inversion, focus, success, fail };

/// Goal state: negative formulas invert eagerly; positive wait for focus.
pub const Goal = struct {
    /// Async (negative) context — inverted first.
    async_ctx: std.ArrayList(*Formula) = .empty,
    /// Sync (positive) context — focused one-at-a-time.
    sync_ctx: std.ArrayList(*Formula) = .empty,
    /// Right-side goal formula (conclusion).
    conclusion: ?*Formula = null,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Goal {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Goal) void {
        self.async_ctx.deinit(self.allocator);
        self.sync_ctx.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn push(self: *Goal, phi: *Formula) !void {
        if (polarity(phi) == .neg) {
            try self.async_ctx.append(self.allocator, phi);
        } else {
            try self.sync_ctx.append(self.allocator, phi);
        }
    }
};

/// One inversion step: decompose a negative formula.
/// Returns true if a rule applied.
pub fn invertStep(goal: *Goal) !bool {
    if (goal.async_ctx.items.len == 0) return false;
    const phi = goal.async_ctx.pop().?;
    switch (phi.*) {
        .with => |w| {
            // &L is invertible in the sense of choosing both branches as goals
            // for the spine we push both conjuncts back as async/sync by polarity
            try goal.push(w.l);
            try goal.push(w.r);
            return true;
        },
        .lolli => |l| {
            // A ⊸ B : treat as consume A (pos) produce B
            try goal.push(l.l);
            try goal.push(l.r);
            return true;
        },
        .top => return true, // ⊤L no-op / ⊤R succeeds when conclusion
        .atom => |a| {
            // Negative atom: leave as suspended identity candidate
            try goal.async_ctx.append(goal.allocator, phi);
            _ = a;
            return false;
        },
        else => {
            try goal.sync_ctx.append(goal.allocator, phi);
            return true;
        },
    }
}

/// Run inversion to quiescence.
pub fn invertAll(goal: *Goal) !void {
    while (try invertStep(goal)) {}
}

/// Focus on the first positive formula: decompose ⊗ / ⊕ / 1.
pub fn focusStep(goal: *Goal) !Phase {
    if (goal.sync_ctx.items.len == 0) {
        // Try identity: matching atoms across async suspended and conclusion
        if (goal.conclusion) |c| {
            if (c.* == .atom) {
                for (goal.async_ctx.items) |a| {
                    if (a.* == .atom and std.mem.eql(u8, a.atom.name, c.atom.name)) {
                        return .success;
                    }
                }
                for (goal.sync_ctx.items) |a| {
                    if (a.* == .atom and std.mem.eql(u8, a.atom.name, c.atom.name)) {
                        return .success;
                    }
                }
            }
            if (c.* == .top) return .success;
        }
        return .fail;
    }
    const phi = goal.sync_ctx.orderedRemove(0);
    switch (phi.*) {
        .tensor => |t| {
            try goal.push(t.l);
            try goal.push(t.r);
            try invertAll(goal);
            return .focus;
        },
        .plus => |p| {
            // ⊕ non-deterministic: try left first
            try goal.push(p.l);
            try invertAll(goal);
            return .focus;
        },
        .one => return .focus, // 1 absorbed
        .zero => return .fail,
        .atom => {
            // Positive atom under focus: must match conclusion
            if (goal.conclusion) |c| {
                if (c.* == .atom and std.mem.eql(u8, phi.atom.name, c.atom.name)) {
                    return .success;
                }
            }
            // Park it
            try goal.sync_ctx.append(goal.allocator, phi);
            return .fail;
        },
        else => {
            try goal.push(phi);
            return .focus;
        },
    }
}

/// Bounded focusing search.
pub fn search(goal: *Goal, max_steps: u32) !Phase {
    try invertAll(goal);
    var steps: u32 = 0;
    while (steps < max_steps) : (steps += 1) {
        const ph = try focusStep(goal);
        if (ph == .success or ph == .fail) return ph;
        try invertAll(goal);
    }
    return .fail;
}

test "polarity of connectives" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.f(.{ .atom = .{ .name = "A", .pol = .pos } });
    const b = try arena.f(.{ .atom = .{ .name = "B", .pol = .neg } });
    const t = try arena.f(.{ .tensor = .{ .l = a, .r = b } });
    const l = try arena.f(.{ .lolli = .{ .l = a, .r = b } });
    try std.testing.expect(polarity(t) == .pos);
    try std.testing.expect(polarity(l) == .neg);
}

test "focus identity atom" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var goal = Goal.init(std.testing.allocator);
    defer goal.deinit();
    const a = try arena.f(.{ .atom = .{ .name = "A", .pol = .pos } });
    try goal.push(a);
    goal.conclusion = a;
    const r = try search(&goal, 8);
    try std.testing.expect(r == .success);
}

test "top conclusion succeeds" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    var goal = Goal.init(std.testing.allocator);
    defer goal.deinit();
    const t = try arena.f(.top);
    goal.conclusion = t;
    const r = try search(&goal, 4);
    try std.testing.expect(r == .success);
}
