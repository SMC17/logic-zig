//! Informal argument analysis — structure first (universal library spine).
//!
//! Not a rhetoric AI: explicit premises, conclusions, scheme tags, support links.
//! Future: schemes library, defeat, dialogue games, natural-language attach.

const std = @import("std");

pub const Scheme = enum {
    unknown,
    modus_ponens,
    modus_tollens,
    disjunctive_syllogism,
    analogy,
    causal,
    authority,
    example,
    practical_means_end,
    conductive,
};

pub const NodeKind = enum { premise, conclusion, intermediate, objection, rebuttal };

pub const NodeId = enum(u32) {
    _,
    pub fn index(self: NodeId) u32 {
        return @intFromEnum(self);
    }
};

pub const Node = struct {
    kind: NodeKind,
    text: []const u8,
    scheme: Scheme = .unknown,
};

pub const Link = struct {
    from: NodeId,
    to: NodeId,
    /// positive support vs attack
    support: bool = true,
};

pub const Argument = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(Node) = .empty,
    links: std.ArrayList(Link) = .empty,

    pub fn init(allocator: std.mem.Allocator) Argument {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Argument) void {
        self.nodes.deinit(self.allocator);
        self.links.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addNode(self: *Argument, kind: NodeKind, text: []const u8, scheme: Scheme) !NodeId {
        const id: NodeId = @enumFromInt(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{ .kind = kind, .text = text, .scheme = scheme });
        return id;
    }

    pub fn addLink(self: *Argument, from: NodeId, to: NodeId, support: bool) !void {
        try self.links.append(self.allocator, .{ .from = from, .to = to, .support = support });
    }

    pub fn conclusionCount(self: *const Argument) u32 {
        var n: u32 = 0;
        for (self.nodes.items) |nd| {
            if (nd.kind == .conclusion) n += 1;
        }
        return n;
    }

    pub fn premiseCount(self: *const Argument) u32 {
        var n: u32 = 0;
        for (self.nodes.items) |nd| {
            if (nd.kind == .premise) n += 1;
        }
        return n;
    }

    /// Structural well-formedness: ≥1 premise, ≥1 conclusion, every conclusion has a support link.
    pub fn structurallyOk(self: *const Argument) bool {
        if (self.premiseCount() == 0 or self.conclusionCount() == 0) return false;
        for (self.nodes.items, 0..) |nd, i| {
            if (nd.kind != .conclusion) continue;
            var has = false;
            for (self.links.items) |lk| {
                if (lk.to.index() == i and lk.support) has = true;
            }
            if (!has) return false;
        }
        return true;
    }
};

/// Encode a tiny MP pattern as informal graph (for demos/tests).
pub fn exampleModusPonens(allocator: std.mem.Allocator) !Argument {
    var a = Argument.init(allocator);
    const p = try a.addNode(.premise, "If P then Q", .modus_ponens);
    const q = try a.addNode(.premise, "P", .unknown);
    const c = try a.addNode(.conclusion, "Q", .modus_ponens);
    try a.addLink(p, c, true);
    try a.addLink(q, c, true);
    return a;
}

test "informal modus ponens structure" {
    var a = try exampleModusPonens(std.testing.allocator);
    defer a.deinit();
    try std.testing.expect(a.structurallyOk());
    try std.testing.expect(a.premiseCount() == 2);
    try std.testing.expect(a.conclusionCount() == 1);
}

test "informal missing support fails" {
    var a = Argument.init(std.testing.allocator);
    defer a.deinit();
    _ = try a.addNode(.premise, "A", .unknown);
    _ = try a.addNode(.conclusion, "B", .unknown);
    try std.testing.expect(!a.structurallyOk());
}
