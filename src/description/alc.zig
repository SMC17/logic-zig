//! Description logic ALC — concepts, roles, TBox/ABox, tableau skeleton.
//!
//! Concept language:
//!   ⊤ | ⊥ | A | ¬C | C ⊓ D | C ⊔ D | ∃R.C | ∀R.C
//!
//! Fragment: concept AST, expansion rules for ∧/∨/∃/∀/¬, clash detection on
//! a single individual (ABox node). Not a full optimized DL reasoner (no
//! blocking strategy industrial suite, no SHIQ).

const std = @import("std");

pub const Concept = union(enum) {
    top,
    bot,
    atom: []const u8,
    not: *Concept,
    and_: struct { l: *Concept, r: *Concept },
    or_: struct { l: *Concept, r: *Concept },
    exists: struct { role: []const u8, filler: *Concept },
    forall: struct { role: []const u8, filler: *Concept },
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*Concept) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }
    pub fn c(self: *Arena, v: Concept) !*Concept {
        const p = try self.allocator.create(Concept);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

pub fn conceptEql(a: *const Concept, b: *const Concept) bool {
    return switch (a.*) {
        .top => b.* == .top,
        .bot => b.* == .bot,
        .atom => |x| switch (b.*) {
            .atom => |y| std.mem.eql(u8, x, y),
            else => false,
        },
        .not => |n| switch (b.*) {
            .not => |m| conceptEql(n, m),
            else => false,
        },
        .and_ => |x| switch (b.*) {
            .and_ => |y| conceptEql(x.l, y.l) and conceptEql(x.r, y.r),
            else => false,
        },
        .or_ => |x| switch (b.*) {
            .or_ => |y| conceptEql(x.l, y.l) and conceptEql(x.r, y.r),
            else => false,
        },
        .exists => |x| switch (b.*) {
            .exists => |y| std.mem.eql(u8, x.role, y.role) and conceptEql(x.filler, y.filler),
            else => false,
        },
        .forall => |x| switch (b.*) {
            .forall => |y| std.mem.eql(u8, x.role, y.role) and conceptEql(x.filler, y.filler),
            else => false,
        },
    };
}

/// Label of an individual: set of concepts asserted to hold.
pub const NodeLabel = struct {
    concepts: std.ArrayList(*Concept),
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) NodeLabel {
        return .{ .concepts = .empty, .allocator = allocator };
    }
    pub fn deinit(self: *NodeLabel) void {
        self.concepts.deinit(self.allocator);
        self.* = undefined;
    }
    pub fn add(self: *NodeLabel, c: *Concept) !void {
        for (self.concepts.items) |x| {
            if (conceptEql(x, c)) return;
        }
        try self.concepts.append(self.allocator, c);
    }
    pub fn hasClash(self: *const NodeLabel) bool {
        for (self.concepts.items) |c| {
            if (c.* == .bot) return true;
            if (c.* == .not) {
                const inner = c.not;
                for (self.concepts.items) |d| {
                    if (conceptEql(d, inner)) return true;
                }
            }
        }
        return false;
    }
};

/// One expansion step: push conjuncts of ⊓ into the label.
pub fn expandAnd(label: *NodeLabel, c: *Concept) !bool {
    switch (c.*) {
        .and_ => |a| {
            try label.add(a.l);
            try label.add(a.r);
            return true;
        },
        else => return false,
    }
}

/// Satisfiability probe: expand all ∧ and detect clash. (∨/∃ branching later.)
pub fn satProbeAnd(allocator: std.mem.Allocator, root: *Concept) !bool {
    var label = NodeLabel.init(allocator);
    defer label.deinit();
    try label.add(root);
    var changed = true;
    while (changed) {
        changed = false;
        var i: usize = 0;
        while (i < label.concepts.items.len) : (i += 1) {
            if (try expandAnd(&label, label.concepts.items[i])) changed = true;
        }
        if (label.hasClash()) return false;
    }
    return true;
}

test "no clash on simple atom" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.c(.{ .atom = "Person" });
    try std.testing.expect(try satProbeAnd(std.testing.allocator, a));
}

test "clash on C and not C" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const a = try arena.c(.{ .atom = "A" });
    const na = try arena.c(.{ .not = a });
    const conj = try arena.c(.{ .and_ = .{ .l = a, .r = na } });
    try std.testing.expect(!try satProbeAnd(std.testing.allocator, conj));
}

test "exists shape" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const person = try arena.c(.{ .atom = "Person" });
    const ex = try arena.c(.{ .exists = .{ .role = "hasChild", .filler = person } });
    try std.testing.expect(ex.* == .exists);
}
