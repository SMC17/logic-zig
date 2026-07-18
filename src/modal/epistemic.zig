//! Multi-agent epistemic logic — S5 model checking with common knowledge
//! and public announcements.
//!
//! A model is a finite set of worlds, a valuation, and one accessibility
//! relation per agent (S5: callers supply equivalence relations; the muddy
//! children builder does). Operators:
//!
//!   K_i φ — agent i knows φ (φ at every i-accessible world);
//!   E_G φ — everybody in G knows φ;
//!   C_G φ — common knowledge: φ at every world reachable by any path
//!           through relations of agents in G (reflexive-transitive closure);
//!   [ψ!]  — public announcement: restrict the model to ψ-worlds.
//!
//! Canon: the muddy children puzzle (n=3, two muddy) — after the father's
//! announcement and one round of "nobody knows", exactly the muddy children
//! know their own state, and it is common knowledge that someone is muddy.

const std = @import("std");

pub const max_worlds = 16;
pub const max_agents = 4;

pub const Model = struct {
    num_worlds: u32,
    num_agents: u32,
    /// alive[w] — world still in the model (announcements delete worlds).
    alive: [max_worlds]bool,
    /// acc[agent][w1][w2] — w2 accessible from w1 for agent.
    acc: [max_agents][max_worlds][max_worlds]bool,
    /// val[w][atom] for atoms 0..31.
    val: [max_worlds]u32,

    pub fn atomTrue(self: *const Model, w: u32, atom: u5) bool {
        return (self.val[w] >> atom) & 1 == 1;
    }
};

pub const Formula = union(enum) {
    atom: u5,
    neg: *const Formula,
    conj: [2]*const Formula,
    disj: [2]*const Formula,
    knows: struct { agent: u32, body: *const Formula },
    /// Common knowledge among all agents.
    common: *const Formula,
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
    pub fn knows(self: *Builder, agent: u32, body: *const Formula) *const Formula {
        return self.mk(.{ .knows = .{ .agent = agent, .body = body } });
    }
    pub fn common(self: *Builder, body: *const Formula) *const Formula {
        return self.mk(.{ .common = body });
    }
};

pub fn holds(m: *const Model, w: u32, f: *const Formula) bool {
    std.debug.assert(m.alive[w]);
    return switch (f.*) {
        .atom => |i| m.atomTrue(w, i),
        .neg => |a| !holds(m, w, a),
        .conj => |p| holds(m, w, p[0]) and holds(m, w, p[1]),
        .disj => |p| holds(m, w, p[0]) or holds(m, w, p[1]),
        .knows => |k| blk: {
            for (0..m.num_worlds) |w2| {
                if (!m.alive[w2]) continue;
                if (m.acc[k.agent][w][w2] and !holds(m, @intCast(w2), k.body)) break :blk false;
            }
            break :blk true;
        },
        .common => |body| blk: {
            // Reachability through the union of all agents' relations.
            var reach: [max_worlds]bool = .{false} ** max_worlds;
            reach[w] = true;
            var changed = true;
            while (changed) {
                changed = false;
                for (0..m.num_worlds) |w1| {
                    if (!reach[w1] or !m.alive[w1]) continue;
                    for (0..m.num_agents) |ag| {
                        for (0..m.num_worlds) |w2| {
                            if (!m.alive[w2] or reach[w2]) continue;
                            if (m.acc[ag][w1][w2]) {
                                reach[w2] = true;
                                changed = true;
                            }
                        }
                    }
                }
            }
            for (0..m.num_worlds) |w2| {
                if (reach[w2] and m.alive[w2] and !holds(m, @intCast(w2), body)) break :blk false;
            }
            break :blk true;
        },
    };
}

/// Public announcement of φ: delete every world where φ fails.
pub fn announce(m: *Model, f: *const Formula) void {
    var keep: [max_worlds]bool = .{false} ** max_worlds;
    for (0..m.num_worlds) |w| {
        if (m.alive[w] and holds(m, @intCast(w), f)) keep[w] = true;
    }
    m.alive = keep;
}

/// Muddy children: worlds = subsets of children, atom i = "child i is muddy".
/// Child i cannot see their own forehead: worlds differing only in bit i are
/// indistinguishable (S5 equivalence classes of size 2).
pub fn muddyChildren(n: u5) Model {
    std.debug.assert(n <= 4);
    var m = Model{
        .num_worlds = @as(u32, 1) << n,
        .num_agents = n,
        .alive = .{false} ** max_worlds,
        .acc = undefined,
        .val = .{0} ** max_worlds,
    };
    for (0..m.num_worlds) |w| {
        m.alive[w] = true;
        m.val[w] = @intCast(w);
    }
    for (0..n) |ag| {
        for (0..m.num_worlds) |w1| {
            for (0..m.num_worlds) |w2| {
                // Same except possibly bit ag (includes reflexive).
                const diff = @as(u32, @intCast(w1)) ^ @as(u32, @intCast(w2));
                m.acc[ag][w1][w2] = diff & ~(@as(u32, 1) << @intCast(ag)) == 0;
            }
        }
    }
    return m;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

/// "Child i knows whether they are muddy": K_i muddy_i ∨ K_i ¬muddy_i.
fn knowsOwnState(b: *Builder, i: u5) *const Formula {
    return b.orF(
        b.knows(i, b.atom(i)),
        b.knows(i, b.notF(b.atom(i))),
    );
}

test "epistemic: muddy children canon (n=3, children 0 and 1 muddy)" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var m = muddyChildren(3);
    const actual: u32 = 0b011; // children 0,1 muddy

    // Before any announcement nobody knows their own state.
    for (0..3) |i| {
        try testing.expect(!holds(&m, actual, knowsOwnState(&b, @intCast(i))));
    }
    // "Someone is muddy" is NOT common knowledge yet (the all-clean world lives).
    const someone = b.orF(b.orF(b.atom(0), b.atom(1)), b.atom(2));
    try testing.expect(!holds(&m, actual, b.common(someone)));

    // Father: "at least one of you is muddy."
    announce(&m, someone);
    try testing.expect(holds(&m, actual, b.common(someone)));
    // Still nobody knows (two muddy children).
    for (0..3) |i| {
        try testing.expect(!holds(&m, actual, knowsOwnState(&b, @intCast(i))));
    }

    // Round 1: everyone announces "I don't know my state."
    const nobody_knows = b.andF(
        b.andF(b.notF(knowsOwnState(&b, 0)), b.notF(knowsOwnState(&b, 1))),
        b.notF(knowsOwnState(&b, 2)),
    );
    announce(&m, nobody_knows);

    // Now exactly the muddy children know; the clean one still doesn't.
    try testing.expect(holds(&m, actual, knowsOwnState(&b, 0)));
    try testing.expect(holds(&m, actual, knowsOwnState(&b, 1)));
    try testing.expect(!holds(&m, actual, knowsOwnState(&b, 2)));
    // And they know they are muddy (not clean).
    try testing.expect(holds(&m, actual, b.knows(0, b.atom(0))));
    try testing.expect(holds(&m, actual, b.knows(1, b.atom(1))));
}

test "epistemic: S5 factivity and positive introspection on muddy model" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var m = muddyChildren(3);
    const actual: u32 = 0b011;
    // Factivity: K_0 φ → φ for φ = "child 1 is muddy" (child 0 sees child 1).
    try testing.expect(holds(&m, actual, b.knows(0, b.atom(1))));
    try testing.expect(holds(&m, actual, b.atom(1)));
    // Positive introspection: K_0 muddy_1 → K_0 K_0 muddy_1.
    try testing.expect(holds(&m, actual, b.knows(0, b.knows(0, b.atom(1)))));
    // Child 0 does not know child 0's state, and knows that they don't...
    // (negative introspection): ¬K_0 muddy_0 → K_0 ¬K_0 muddy_0.
    try testing.expect(!holds(&m, actual, b.knows(0, b.atom(0))));
    try testing.expect(holds(&m, actual, b.knows(0, b.notF(b.knows(0, b.atom(0))))));
}

test "epistemic: common knowledge is stronger than everybody-knows" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    var m = muddyChildren(2);
    const actual: u32 = 0b11; // both muddy
    const someone = b.orF(b.atom(0), b.atom(1));
    // Each child sees the other: everybody knows someone is muddy.
    try testing.expect(holds(&m, actual, b.knows(0, someone)));
    try testing.expect(holds(&m, actual, b.knows(1, someone)));
    // But it is not common knowledge (⊥-world reachable in two steps).
    try testing.expect(!holds(&m, actual, b.common(someone)));
    announce(&m, someone);
    try testing.expect(holds(&m, actual, b.common(someone)));
}
