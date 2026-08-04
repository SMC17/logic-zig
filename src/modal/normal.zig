//! Normal modal logics K, T, S4, S5 — finite-frame decision procedure.
//!
//! For a propositional modal formula, decide validity in the class by
//! enumerating all frames up to n worlds (filtration bound) and checking
//! whether every world forces the formula under every valuation.
//!
//! Frame conditions:
//!   K  — no restriction
//!   T  — reflexive
//!   S4 — reflexive + transitive
//!   S5 — equivalence (refl + sym + trans)
//!
//! Fragment: n ≤ 4 worlds, ≤ 3 atoms (exhaustive 2^(n²) relations filtered).
//! Complete for the admitted finite bound; not a tableau with certificates yet.

const std = @import("std");

pub const System = enum { k, t, s4, s5 };

pub const Formula = union(enum) {
    atom: u32,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    implies: struct { l: *Formula, r: *Formula },
    box: *Formula,
    dia: *Formula,
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

fn forces(n: u32, rel: u32, val: u32, w: u32, phi: *const Formula) bool {
    return switch (phi.*) {
        .atom => |a| (val & (@as(u32, 1) << @intCast(a * n + w))) != 0,
        .not => |x| !forces(n, rel, val, w, x),
        .and_ => |x| forces(n, rel, val, w, x.l) and forces(n, rel, val, w, x.r),
        .or_ => |x| forces(n, rel, val, w, x.l) or forces(n, rel, val, w, x.r),
        .implies => |x| !forces(n, rel, val, w, x.l) or forces(n, rel, val, w, x.r),
        .box => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and !forces(n, rel, val, v, x)) break :blk false;
            }
            break :blk true;
        },
        .dia => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and forces(n, rel, val, v, x)) break :blk true;
            }
            break :blk false;
        },
    };
}

fn reflexive(n: u32, rel: u32) bool {
    var w: u32 = 0;
    while (w < n) : (w += 1) {
        if ((rel & (@as(u32, 1) << @intCast(w * n + w))) == 0) return false;
    }
    return true;
}

fn symmetric(n: u32, rel: u32) bool {
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        var j: u32 = 0;
        while (j < n) : (j += 1) {
            const ij = (rel & (@as(u32, 1) << @intCast(i * n + j))) != 0;
            const ji = (rel & (@as(u32, 1) << @intCast(j * n + i))) != 0;
            if (ij != ji) return false;
        }
    }
    return true;
}

fn transitive(n: u32, rel: u32) bool {
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        var j: u32 = 0;
        while (j < n) : (j += 1) {
            var k: u32 = 0;
            while (k < n) : (k += 1) {
                const ij = (rel & (@as(u32, 1) << @intCast(i * n + j))) != 0;
                const jk = (rel & (@as(u32, 1) << @intCast(j * n + k))) != 0;
                const ik = (rel & (@as(u32, 1) << @intCast(i * n + k))) != 0;
                if (ij and jk and !ik) return false;
            }
        }
    }
    return true;
}

fn okFrame(sys: System, n: u32, rel: u32) bool {
    return switch (sys) {
        .k => true,
        .t => reflexive(n, rel),
        .s4 => reflexive(n, rel) and transitive(n, rel),
        .s5 => reflexive(n, rel) and symmetric(n, rel) and transitive(n, rel),
    };
}

pub const Decision = enum { valid, invalid, bound_exceeded };

/// Decide validity of phi in system over frames of size ≤ max_n and atoms ≤ max_atoms.
pub fn decide(sys: System, phi: *const Formula, n_atoms: u32, max_n: u32) Decision {
    if (max_n > 4 or n_atoms > 3) return .bound_exceeded;
    var n: u32 = 1;
    while (n <= max_n) : (n += 1) {
        const rel_bits = n * n;
        const rel_full: u32 = if (rel_bits >= 32) 0xFFFF_FFFF else (@as(u32, 1) << @intCast(rel_bits)) - 1;
        var rel: u32 = 0;
        while (rel <= rel_full) : (rel += 1) {
            if (!okFrame(sys, n, rel)) continue;
            const val_bits = n_atoms * n;
            const val_full: u32 = if (val_bits >= 32) 0xFFFF_FFFF else (@as(u32, 1) << @intCast(val_bits)) - 1;
            var val: u32 = 0;
            while (val <= val_full) : (val += 1) {
                var w: u32 = 0;
                while (w < n) : (w += 1) {
                    if (!forces(n, rel, val, w, phi)) return .invalid;
                }
            }
            if (rel == rel_full) break;
        }
    }
    return .valid;
}

test "box p implies p is T-valid not K-valid" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const bp = try arena.f(.{ .box = p });
    const imp = try arena.f(.{ .implies = .{ .l = bp, .r = p } });
    // On 1–2 worlds: T requires refl so □p→p holds; K allows irreflexive countermodel
    try std.testing.expect(decide(.t, imp, 1, 2) == .valid);
    try std.testing.expect(decide(.k, imp, 1, 2) == .invalid);
}

test "p implies box p fails T" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const bp = try arena.f(.{ .box = p });
    const imp = try arena.f(.{ .implies = .{ .l = p, .r = bp } });
    try std.testing.expect(decide(.t, imp, 1, 2) == .invalid);
}

test "atom is not valid" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    try std.testing.expect(decide(.s5, p, 1, 1) == .invalid);
}
