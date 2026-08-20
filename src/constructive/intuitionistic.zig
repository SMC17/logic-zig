//! Intuitionistic propositional logic (IPC) — finite Kripke semantics.
//!
//! Classical LEM (A ∨ ¬A) and double-negation elimination fail.
//! A world forces:
//!   atom    — monotone valuation
//!   A ∧ B   — forces A and B
//!   A ∨ B   — forces A or B
//!   A → B   — every accessible w' forcing A forces B
//!   ¬A      — A → ⊥
//!
//! Fragment: finite frames + forcing evaluator + LEM-failure witness.

const std = @import("std");

pub const Formula = union(enum) {
    atom: u32,
    bot,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    implies: struct { l: *Formula, r: *Formula },
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

/// Finite intuitionistic Kripke frame: worlds, accessibility (preorder), valuation.
pub const Frame = struct {
    n_worlds: u32,
    /// access[w] = bitmask of worlds ≥ w (reflexive transitive).
    access: []u32,
    /// val[atom] = bitmask of worlds forcing the atom (must be upset).
    val: []u32,

    pub fn forces(self: *const Frame, w: u32, phi: *const Formula) bool {
        return switch (phi.*) {
            .bot => false,
            .atom => |a| (self.val[a] & (@as(u32, 1) << @intCast(w))) != 0,
            .not => |n| blk: {
                // ¬A at w iff no accessible w' forces A
                const acc = self.access[w];
                var v: u32 = 0;
                while (v < self.n_worlds) : (v += 1) {
                    if ((acc & (@as(u32, 1) << @intCast(v))) != 0) {
                        if (self.forces(v, n)) break :blk false;
                    }
                }
                break :blk true;
            },
            .and_ => |a| self.forces(w, a.l) and self.forces(w, a.r),
            .or_ => |a| self.forces(w, a.l) or self.forces(w, a.r),
            .implies => |a| blk: {
                const acc = self.access[w];
                var v: u32 = 0;
                while (v < self.n_worlds) : (v += 1) {
                    if ((acc & (@as(u32, 1) << @intCast(v))) != 0) {
                        if (self.forces(v, a.l) and !self.forces(v, a.r)) break :blk false;
                    }
                }
                break :blk true;
            },
        };
    }

    pub fn valid(self: *const Frame, phi: *const Formula) bool {
        var w: u32 = 0;
        while (w < self.n_worlds) : (w += 1) {
            if (!self.forces(w, phi)) return false;
        }
        return true;
    }
};

/// Classic countermodel: 2-world chain 0 ≤ 1, atom p forced only at 1.
/// Then p ∨ ¬p fails at 0.
pub fn lemCountermodel(allocator: std.mem.Allocator) !struct { frame: Frame, formula: *Formula, arena: Arena } {
    var arena = Arena.init(allocator);
    errdefer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const np = try arena.f(.{ .not = p });
    const lem = try arena.f(.{ .or_ = .{ .l = p, .r = np } });

    const access = try allocator.alloc(u32, 2);
    access[0] = 0b11; // 0 sees 0 and 1
    access[1] = 0b10; // 1 sees 1
    const val = try allocator.alloc(u32, 1);
    val[0] = 0b10; // p only at world 1

    return .{
        .frame = .{ .n_worlds = 2, .access = access, .val = val },
        .formula = lem,
        .arena = arena,
    };
}

test "LEM fails on chain countermodel" {
    var cm = try lemCountermodel(std.testing.allocator);
    defer cm.arena.deinit();
    defer std.testing.allocator.free(cm.frame.access);
    defer std.testing.allocator.free(cm.frame.val);
    try std.testing.expect(!cm.frame.forces(0, cm.formula));
    try std.testing.expect(cm.frame.forces(1, cm.formula));
    try std.testing.expect(!cm.frame.valid(cm.formula));
}

test "atom upset forced at 1" {
    var cm = try lemCountermodel(std.testing.allocator);
    defer cm.arena.deinit();
    defer std.testing.allocator.free(cm.frame.access);
    defer std.testing.allocator.free(cm.frame.val);
    const p = try cm.arena.f(.{ .atom = 0 });
    try std.testing.expect(cm.frame.forces(1, p));
    try std.testing.expect(!cm.frame.forces(0, p));
}
