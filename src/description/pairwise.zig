//! Pairwise blocking and qualified number-restriction expansion for SHIQ.
!
//! Pairwise blocking (Horrocks/Sattler): node x is blocked by ancestor y when
//! label(x) ⊆ label(y) and for every R-neighbor x' of x there is an R-neighbor
//! y' of y with label(x') ⊆ label(y') (and symmetrically for inverses in full SHIQ).
//!
//! Fragment: pairwise condition on the completion tree from `shiq_tableau`,
//! plus ≥n R.C expansion creating n distinct successors. ≤n is clash-checked
//! by counting R-neighbors of type C.

const std = @import("std");
const alc = @import("alc.zig");
const tab = @import("shiq_tableau.zig");
const shiq = @import("shiq.zig");

fn labelSubset(small: []const *alc.Concept, big: []const *alc.Concept) bool {
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

/// Pairwise block: ancestor y blocks x.
pub fn pairwiseBlocked(t: *const tab.Tableau, x: tab.NodeId, y: tab.NodeId) bool {
    if (!labelSubset(t.nodes.items[x].label.items, t.nodes.items[y].label.items)) return false;
    // For each edge x --R--> x', need y --R--> y' with label(x') ⊆ label(y')
    for (t.edges.items) |ex| {
        if (ex.from != x) continue;
        var matched = false;
        for (t.edges.items) |ey| {
            if (ey.from != y) continue;
            if (!std.mem.eql(u8, ex.role, ey.role)) continue;
            if (labelSubset(t.nodes.items[ex.to].label.items, t.nodes.items[ey.to].label.items)) {
                matched = true;
                break;
            }
        }
        if (!matched) return false;
    }
    return true;
}

pub fn applyPairwiseBlocking(t: *tab.Tableau) void {
    for (t.nodes.items, 0..) |*node, i| {
        node.blocked = false;
        var anc = node.parent;
        while (anc) |a| {
            if (pairwiseBlocked(t, @intCast(i), a)) {
                node.blocked = true;
                break;
            }
            anc = t.nodes.items[a].parent;
        }
    }
}

/// Expand ≥n R.C on node: ensure at least n distinct R-successors carrying C.
pub fn expandAtLeast(
    t: *tab.Tableau,
    node: tab.NodeId,
    n: u32,
    role: []const u8,
    filler: *alc.Concept,
) !bool {
    var count: u32 = 0;
    for (t.edges.items) |e| {
        if (e.from == node and std.mem.eql(u8, e.role, role)) count += 1;
    }
    var changed = false;
    while (count < n) : (count += 1) {
        const succ = try t.addNode(node);
        try t.edges.append(t.allocator, .{ .from = node, .to = succ, .role = role });
        try t.addConcept(succ, filler);
        changed = true;
    }
    return changed;
}

/// Clash if ≤n R.C and more than n R-neighbors already typed C (approx: all R-neighbors).
pub fn checkAtMostClash(t: *const tab.Tableau, node: tab.NodeId, n: u32, role: []const u8) bool {
    var count: u32 = 0;
    for (t.edges.items) |e| {
        if (e.from == node and std.mem.eql(u8, e.role, role)) count += 1;
    }
    return count > n;
}

test "pairwise reduces to subset when no edges" {
    var t = tab.Tableau.init(std.testing.allocator);
    defer t.deinit();
    var arena = alc.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.c(.{ .atom = "A" });
    const root = try t.addNode(null);
    const child = try t.addNode(root);
    try t.addConcept(root, a);
    try t.addConcept(child, a);
    // child label ⊆ root label, no edges → pairwise holds
    try std.testing.expect(pairwiseBlocked(&t, child, root));
}

test "at-least creates n successors" {
    var t = tab.Tableau.init(std.testing.allocator);
    defer t.deinit();
    var arena = alc.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.c(.{ .atom = "P" });
    const root = try t.addNode(null);
    _ = try expandAtLeast(&t, root, 3, "R", p);
    var n: u32 = 0;
    for (t.edges.items) |e| {
        if (e.from == root) n += 1;
    }
    try std.testing.expect(n == 3);
}
