//! SHIQ description logic — roles with hierarchy, inverse, transitivity,
//! and qualified number restrictions on top of ALC.
//!
//! SHIQ = ALC + role hierarchy (H) + inverse roles (I) + qualified ≥/≤ (Q)
//!        + transitive roles (S ⊃ R₊).
//!
//! Fragment: role axiom AST, concept language with ≥n R.C / ≤n R.C,
//! simple hierarchy closure, inverse pairing. Not a full optimized SHIQ
//! tableau with pairwise blocking (Horrocks/Sattler).

const std = @import("std");
const alc = @import("alc.zig");

pub const Role = struct {
    name: []const u8,
    transitive: bool = false,
    inverse_of: ?[]const u8 = null,
};

pub const RoleAxiom = union(enum) {
    /// R ⊑ S
    sub: struct { sub: []const u8, sup: []const u8 },
    /// Trans(R)
    trans: []const u8,
    /// R⁻ ≡ S (inverse)
    inv: struct { role: []const u8, inv: []const u8 },
};

pub const Concept = union(enum) {
    alc: *alc.Concept,
    /// ≥ n R.C
    at_least: struct { n: u32, role: []const u8, filler: *Concept },
    /// ≤ n R.C
    at_most: struct { n: u32, role: []const u8, filler: *Concept },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*Concept) = .empty,
    alc_arena: alc.Arena,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator, .alc_arena = alc.Arena.init(allocator) };
    }
    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.alc_arena.deinit();
        self.* = undefined;
    }
    pub fn c(self: *Arena, v: Concept) !*Concept {
        const p = try self.allocator.create(Concept);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

/// Role hierarchy: adjacency list name → list of superrole names.
pub const Hierarchy = struct {
    supers: std.StringHashMap(std.ArrayList([]const u8)),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Hierarchy {
        return .{ .supers = std.StringHashMap(std.ArrayList([]const u8)).init(allocator), .allocator = allocator };
    }
    pub fn deinit(self: *Hierarchy) void {
        var it = self.supers.iterator();
        while (it.next()) |e| e.value_ptr.deinit(self.allocator);
        self.supers.deinit();
        self.* = undefined;
    }
    pub fn addSub(self: *Hierarchy, sub: []const u8, sup: []const u8) !void {
        const gop = try self.supers.getOrPut(sub);
        if (!gop.found_existing) gop.value_ptr.* = .empty;
        try gop.value_ptr.append(self.allocator, sup);
    }
    /// Reflexive-transitive: is `sub` ≤ `sup`?
    pub fn isSubRole(self: *const Hierarchy, sub: []const u8, sup: []const u8) bool {
        if (std.mem.eql(u8, sub, sup)) return true;
        var stack: [32][]const u8 = undefined;
        var sp: usize = 0;
        stack[sp] = sub;
        sp += 1;
        var seen: u32 = 0;
        while (sp > 0 and seen < 32) {
            sp -= 1;
            const cur = stack[sp];
            seen += 1;
            if (self.supers.get(cur)) |list| {
                for (list.items) |s| {
                    if (std.mem.eql(u8, s, sup)) return true;
                    if (sp < 32) {
                        stack[sp] = s;
                        sp += 1;
                    }
                }
            }
        }
        return false;
    }
};

/// TBox + role axioms container.
pub const ShiqKb = struct {
    roles: []const Role,
    axioms: []const RoleAxiom,
    hierarchy: Hierarchy,

    pub fn buildHierarchy(self: *ShiqKb) !void {
        for (self.axioms) |ax| {
            switch (ax) {
                .sub => |s| try self.hierarchy.addSub(s.sub, s.sup),
                .trans, .inv => {},
            }
        }
    }

    pub fn isTransitive(self: *const ShiqKb, name: []const u8) bool {
        for (self.roles) |r| {
            if (std.mem.eql(u8, r.name, name) and r.transitive) return true;
        }
        for (self.axioms) |ax| {
            if (ax == .trans and std.mem.eql(u8, ax.trans, name)) return true;
        }
        return false;
    }

    pub fn inverse(self: *const ShiqKb, name: []const u8) ?[]const u8 {
        for (self.roles) |r| {
            if (std.mem.eql(u8, r.name, name)) return r.inverse_of;
        }
        for (self.axioms) |ax| {
            if (ax == .inv and std.mem.eql(u8, ax.inv.role, name)) return ax.inv.inv;
        }
        return null;
    }
};

test "role hierarchy closure" {
    var h = Hierarchy.init(std.testing.allocator);
    defer h.deinit();
    try h.addSub("hasChild", "hasDescendant");
    try h.addSub("hasDescendant", "hasRelative");
    try std.testing.expect(h.isSubRole("hasChild", "hasRelative"));
    try std.testing.expect(h.isSubRole("hasChild", "hasChild"));
    try std.testing.expect(!h.isSubRole("hasRelative", "hasChild"));
}

test "transitive flag" {
    const roles = [_]Role{
        .{ .name = "ancestor", .transitive = true },
        .{ .name = "parent", .transitive = false },
    };
    var kb = ShiqKb{
        .roles = &roles,
        .axioms = &[_]RoleAxiom{},
        .hierarchy = Hierarchy.init(std.testing.allocator),
    };
    defer kb.hierarchy.deinit();
    try std.testing.expect(kb.isTransitive("ancestor"));
    try std.testing.expect(!kb.isTransitive("parent"));
}

test "at-least concept shape" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const person = try arena.alc_arena.c(.{ .atom = "Person" });
    const filler = try arena.c(.{ .alc = person });
    const ge2 = try arena.c(.{ .at_least = .{ .n = 2, .role = "hasChild", .filler = filler } });
    try std.testing.expect(ge2.at_least.n == 2);
}
