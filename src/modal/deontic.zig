//! Standard deontic logic (SDL) — the modal logic KD on finite serial frames.
//!
//! O φ ("obligatory") is □ over an accessibility relation whose successors are
//! the deontically ideal alternatives; P φ ("permitted") is ◇. SDL = K + the
//! D axiom (O φ → P φ), which corresponds exactly to **seriality** (every
//! world has at least one ideal alternative — no normative dead ends).
//!
//! The engine evaluates formulas on finite frames and checks frame validity;
//! `seriality` is a decidable frame check. Canon covered: O/P duality, the D
//! axiom on serial frames (and its failure on non-serial ones), K
//! distribution, Ross's inference O p ⊢ O(p∨q) — *valid* in SDL, which is
//! precisely why it is called a paradox — and the no-conflicts theorem
//! ¬(Op ∧ O¬p) on serial frames.

const std = @import("std");

pub const max_worlds = 16;

pub const Frame = struct {
    num_worlds: u32,
    /// ideal[w1][w2] — w2 is a deontically ideal alternative to w1.
    ideal: [max_worlds][max_worlds]bool,
    /// val[w] — atom bitmask at world w.
    val: [max_worlds]u32,
};

pub const Formula = union(enum) {
    atom: u5,
    neg: *const Formula,
    conj: [2]*const Formula,
    disj: [2]*const Formula,
    /// O φ — obligatory.
    ob: *const Formula,
    /// P φ — permitted (¬O¬φ; primitive for convenience).
    perm: *const Formula,
};

pub const Builder = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .arena = std.heap.ArenaAllocator.init(allocator) };
    }
    pub fn deinit(self: *Builder) void {
        self.arena.deinit();
    }
    fn mk(self: *Builder, f: Formula) *const Formula {
        const p = self.arena.allocator().create(Formula) catch @panic("oom");
        p.* = f;
        return p;
    }
    pub fn atom(self: *Builder, i: u5) *const Formula {
        return self.mk(.{ .atom = i });
    }
    pub fn notF(self: *Builder, a: *const Formula) *const Formula {
        return self.mk(.{ .neg = a });
    }
    pub fn andF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .conj = .{ a, b } });
    }
    pub fn orF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.mk(.{ .disj = .{ a, b } });
    }
    pub fn impF(self: *Builder, a: *const Formula, b: *const Formula) *const Formula {
        return self.orF(self.notF(a), b);
    }
    pub fn obF(self: *Builder, a: *const Formula) *const Formula {
        return self.mk(.{ .ob = a });
    }
    pub fn permF(self: *Builder, a: *const Formula) *const Formula {
        return self.mk(.{ .perm = a });
    }
};

pub fn holds(fr: *const Frame, w: u32, f: *const Formula) bool {
    return switch (f.*) {
        .atom => |i| (fr.val[w] >> i) & 1 == 1,
        .neg => |a| !holds(fr, w, a),
        .conj => |p| holds(fr, w, p[0]) and holds(fr, w, p[1]),
        .disj => |p| holds(fr, w, p[0]) or holds(fr, w, p[1]),
        .ob => |a| blk: {
            for (0..fr.num_worlds) |w2| {
                if (fr.ideal[w][w2] and !holds(fr, @intCast(w2), a)) break :blk false;
            }
            break :blk true;
        },
        .perm => |a| blk: {
            for (0..fr.num_worlds) |w2| {
                if (fr.ideal[w][w2] and holds(fr, @intCast(w2), a)) break :blk true;
            }
            break :blk false;
        },
    };
}

/// Valid on the frame: true at every world.
pub fn validOnFrame(fr: *const Frame, f: *const Formula) bool {
    for (0..fr.num_worlds) |w| {
        if (!holds(fr, @intCast(w), f)) return false;
    }
    return true;
}

/// D-frame check: every world has an ideal alternative.
pub fn serial(fr: *const Frame) bool {
    for (0..fr.num_worlds) |w1| {
        var any = false;
        for (0..fr.num_worlds) |w2| {
            if (fr.ideal[w1][w2]) {
                any = true;
                break;
            }
        }
        if (!any) return false;
    }
    return true;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

/// 3-world serial fixture: world 0 (actual, p∧¬q), ideals 1 (p), 2 (p,q);
/// ideals point to themselves (idealized worlds are self-consistent).
fn fixture() Frame {
    var fr = Frame{
        .num_worlds = 3,
        .ideal = std.mem.zeroes([max_worlds][max_worlds]bool),
        .val = std.mem.zeroes([max_worlds]u32),
    };
    fr.ideal[0][1] = true;
    fr.ideal[0][2] = true;
    fr.ideal[1][1] = true;
    fr.ideal[2][2] = true;
    fr.val[0] = 0b001; // p, ¬q
    fr.val[1] = 0b001; // p
    fr.val[2] = 0b011; // p, q
    return fr;
}

test "deontic: O/P duality and basic obligations" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const fr = fixture();
    const p = b.atom(0);
    const q = b.atom(1);
    // O p at world 0 (p in both ideals); ¬O q (q fails in ideal 1).
    try testing.expect(holds(&fr, 0, b.obF(p)));
    try testing.expect(!holds(&fr, 0, b.obF(q)));
    // P q (q in ideal 2); duality Pφ ≡ ¬O¬φ frame-wide.
    try testing.expect(holds(&fr, 0, b.permF(q)));
    const dual1 = b.impF(b.permF(q), b.notF(b.obF(b.notF(q))));
    const dual2 = b.impF(b.notF(b.obF(b.notF(q))), b.permF(q));
    try testing.expect(validOnFrame(&fr, dual1));
    try testing.expect(validOnFrame(&fr, dual2));
}

test "deontic: D axiom holds on serial frames, fails without seriality" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const p = b.atom(0);
    const d_axiom = b.impF(b.obF(p), b.permF(p));
    var fr = fixture();
    try testing.expect(serial(&fr));
    try testing.expect(validOnFrame(&fr, d_axiom));
    // No-conflict theorem on serial frames: ¬(Op ∧ O¬p).
    try testing.expect(validOnFrame(&fr, b.notF(b.andF(b.obF(p), b.obF(b.notF(p))))));
    // Break seriality: world 1 loses its ideal.
    fr.ideal[1][1] = false;
    try testing.expect(!serial(&fr));
    // At a dead-end world O p holds vacuously but P p fails → D fails there.
    try testing.expect(!validOnFrame(&fr, d_axiom));
}

test "deontic: K distribution and Ross's inference are SDL-valid" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const fr = fixture();
    const p = b.atom(0);
    const q = b.atom(1);
    // K: O(p→q) → (Op → Oq).
    const k_axiom = b.impF(b.obF(b.impF(p, q)), b.impF(b.obF(p), b.obF(q)));
    try testing.expect(validOnFrame(&fr, k_axiom));
    // Ross: Op → O(p∨q). Valid in SDL — the "paradox" is that mailing the
    // letter obligates mailing-or-burning; SDL bites this bullet.
    try testing.expect(validOnFrame(&fr, b.impF(b.obF(p), b.obF(b.orF(p, q)))));
    // But the converse O(p∨q) → Op is NOT valid: q-only ideal breaks it.
    var fr2 = fixture();
    fr2.val[1] = 0b010; // ideal 1: ¬p, q
    try testing.expect(!validOnFrame(&fr2, b.impF(b.obF(b.orF(p, q)), b.obF(p))));
}
