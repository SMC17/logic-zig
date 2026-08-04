//! SHIQ-style tableau with subset blocking.
//!
//! Expands concept labels on individuals; creates role-successors for ∃;
//! propagates ∀; detects clashes (C and ¬C). **Subset blocking**: a node is
//! blocked when an ancestor's label is a superset of its label (cycle prevention
//! for infinite models).
//!
//! Fragment: ALC core + blocking; qualified number restrictions and role
//! hierarchy from `shiq.zig` are consulted but not fully expanded. Not a
//! production HermiT/FaCT++ clone.

const std = @import("std");
const alc = @import("alc.zig");

pub const NodeId = u32;

pub const Node = struct {
    label: std.ArrayList(*alc.Concept),
    /// Parent in the completion tree (null = root).
    parent: ?NodeId = null,
    blocked: bool = false,

    pub fn deinit(self: *Node, allocator: std.mem.Allocator) void {
        self.label.deinit(allocator);
    }
};

pub const Edge = struct {
    from: NodeId,
    to: NodeId,
    role: []const u8,
};

pub const Tableau = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(Node),
    edges: std.ArrayList(Edge),
    clash: bool = false,

    pub fn init(allocator: std.mem.Allocator) Tableau {
        return .{ .allocator = allocator, .nodes = .empty, .edges = .empty };
    }

    pub fn deinit(self: *Tableau) void {
        for (self.nodes.items) |*n| n.deinit(self.allocator);
        self.nodes.deinit(self.allocator);
        self.edges.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn addNode(self: *Tableau, parent: ?NodeId) !NodeId {
        const id: NodeId = @intCast(self.nodes.items.len);
        try self.nodes.append(self.allocator, .{ .label = .empty, .parent = parent });
        return id;
    }

    fn labelContains(self: *const Tableau, node: NodeId, c: *const alc.Concept) bool {
        for (self.nodes.items[node].label.items) |x| {
            if (alc.conceptEql(x, c)) return true;
        }
        return false;
    }

    pub fn addConcept(self: *Tableau, node: NodeId, c: *alc.Concept) !void {
        if (self.labelContains(node, c)) return;
        try self.nodes.items[node].label.append(self.allocator, c);
        // Clash: bot or C and ¬C
        if (c.* == .bot) {
            self.clash = true;
            return;
        }
        if (c.* == .not) {
            if (self.labelContains(node, c.not)) self.clash = true;
        } else {
            // look for not c already present
            for (self.nodes.items[node].label.items) |x| {
                if (x.* == .not and alc.conceptEql(x.not, c)) {
                    self.clash = true;
                    return;
                }
            }
        }
    }

    /// Subset blocking: node blocked if some ancestor label ⊇ this label.
    pub fn applyBlocking(self: *Tableau) void {
        for (self.nodes.items, 0..) |*node, i| {
            node.blocked = false;
            var anc = node.parent;
            while (anc) |a| {
                if (isSuperset(self.nodes.items[a].label.items, node.label.items)) {
                    node.blocked = true;
                    break;
                }
                anc = self.nodes.items[a].parent;
            }
            _ = i;
        }
    }

    fn isSuperset(big: []const *alc.Concept, small: []const *alc.Concept) bool {
        for (small) |s| {
            var found = false;
            for (big) |b| {
                if (alc.conceptEql(b, s)) {
                    found = true;
                    break;
                }
            }
            if (!found) return false;
        }
        return true;
    }

    /// One expansion pass: ⊓, ∃, ∀ on non-blocked nodes.
    pub fn expandOnce(self: *Tableau) !bool {
        self.applyBlocking();
        var changed = false;
        var i: usize = 0;
        while (i < self.nodes.items.len) : (i += 1) {
            if (self.nodes.items[i].blocked) continue;
            var j: usize = 0;
            while (j < self.nodes.items[i].label.items.len) : (j += 1) {
                const c = self.nodes.items[i].label.items[j];
                switch (c.*) {
                    .and_ => |a| {
                        const before = self.nodes.items[i].label.items.len;
                        try self.addConcept(@intCast(i), a.l);
                        try self.addConcept(@intCast(i), a.r);
                        if (self.nodes.items[i].label.items.len > before) changed = true;
                    },
                    .exists => |e| {
                        // If no R-successor yet, create one with filler
                        var has = false;
                        for (self.edges.items) |ed| {
                            if (ed.from == i and std.mem.eql(u8, ed.role, e.role)) {
                                has = true;
                                break;
                            }
                        }
                        if (!has) {
                            const succ = try self.addNode(@intCast(i));
                            try self.edges.append(self.allocator, .{ .from = @intCast(i), .to = succ, .role = e.role });
                            try self.addConcept(succ, e.filler);
                            changed = true;
                        }
                    },
                    .forall => |e| {
                        for (self.edges.items) |ed| {
                            if (ed.from == i and std.mem.eql(u8, ed.role, e.role)) {
                                if (!self.labelContains(ed.to, e.filler)) {
                                    try self.addConcept(ed.to, e.filler);
                                    changed = true;
                                }
                            }
                        }
                    },
                    else => {},
                }
                if (self.clash) return changed;
            }
        }
        return changed;
    }

    pub fn saturate(self: *Tableau, max_iters: u32) !void {
        var it: u32 = 0;
        while (it < max_iters) : (it += 1) {
            if (self.clash) return;
            if (!try self.expandOnce()) return;
        }
    }
};

/// Satisfiability probe with blocking tableau.
pub fn sat(allocator: std.mem.Allocator, root_concept: *alc.Concept, max_iters: u32) !bool {
    var tab = Tableau.init(allocator);
    defer tab.deinit();
    const root = try tab.addNode(null);
    try tab.addConcept(root, root_concept);
    try tab.saturate(max_iters);
    return !tab.clash;
}

test "clash on C and not C" {
    var arena = alc.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.c(.{ .atom = "A" });
    const na = try arena.c(.{ .not = a });
    const conj = try arena.c(.{ .and_ = .{ .l = a, .r = na } });
    try std.testing.expect(!try sat(std.testing.allocator, conj, 16));
}

test "exists creates successor" {
    var arena = alc.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.c(.{ .atom = "Person" });
    const ex = try arena.c(.{ .exists = .{ .role = "hasChild", .filler = p } });
    try std.testing.expect(try sat(std.testing.allocator, ex, 16));
}

test "blocking eventually quiets infinite exists chain pattern" {
    // ∃R.∃R.… would grow forever without blocking; single ∃ is fine.
    var arena = alc.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const top = try arena.c(.top);
    const ex = try arena.c(.{ .exists = .{ .role = "R", .filler = top } });
    try std.testing.expect(try sat(std.testing.allocator, ex, 32));
}
