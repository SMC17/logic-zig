//! Epistemic and deontic modal logic — multi-agent Kripke fragment.
//!
//! Epistemic: K_i φ  (“agent i knows φ”) — truth in all i-accessible worlds.
//! Deontic:   O φ    (“φ is obligatory") — truth in all ideal/deontically accessible worlds.
//!            P φ    (“φ is permitted")  — truth in some ideal world.
//!
//! Frame conditions (documented, partially enforced):
//!   Epistemic S5-ish: reflexive + transitive + symmetric per agent (optional flags).
//!   Deontic D: serial (every world has an ideal successor).
//!
//! Fragment: finite multi-relation frames + forcing evaluator.

const std = @import("std");

pub const Formula = union(enum) {
    atom: u32,
    not: *Formula,
    and_: struct { l: *Formula, r: *Formula },
    or_: struct { l: *Formula, r: *Formula },
    implies: struct { l: *Formula, r: *Formula },
    /// K_agent φ
    knows: struct { agent: u32, body: *Formula },
    /// O φ
    obligatory: *Formula,
    /// P φ
    permitted: *Formula,
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

pub const MultiFrame = struct {
    n_worlds: u32,
    n_agents: u32,
    /// epistemic[agent][world] = bitmask of accessible worlds
    epistemic: [][]u32,
    /// deontic[world] = bitmask of ideal worlds
    deontic: []u32,
    /// val[atom] = bitmask of worlds where atom holds
    val: []u32,

    pub fn forces(self: *const MultiFrame, w: u32, phi: *const Formula) bool {
        return switch (phi.*) {
            .atom => |a| (self.val[a] & (@as(u32, 1) << @intCast(w))) != 0,
            .not => |n| !self.forces(w, n),
            .and_ => |a| self.forces(w, a.l) and self.forces(w, a.r),
            .or_ => |a| self.forces(w, a.l) or self.forces(w, a.r),
            .implies => |a| !self.forces(w, a.l) or self.forces(w, a.r),
            .knows => |k| blk: {
                const acc = self.epistemic[k.agent][w];
                var v: u32 = 0;
                while (v < self.n_worlds) : (v += 1) {
                    if ((acc & (@as(u32, 1) << @intCast(v))) != 0) {
                        if (!self.forces(v, k.body)) break :blk false;
                    }
                }
                break :blk true;
            },
            .obligatory => |body| blk: {
                const acc = self.deontic[w];
                var v: u32 = 0;
                while (v < self.n_worlds) : (v += 1) {
                    if ((acc & (@as(u32, 1) << @intCast(v))) != 0) {
                        if (!self.forces(v, body)) break :blk false;
                    }
                }
                break :blk true;
            },
            .permitted => |body| blk: {
                const acc = self.deontic[w];
                var v: u32 = 0;
                while (v < self.n_worlds) : (v += 1) {
                    if ((acc & (@as(u32, 1) << @intCast(v))) != 0) {
                        if (self.forces(v, body)) break :blk true;
                    }
                }
                break :blk false;
            },
        };
    }

    /// Serial deontic: every world has ≥1 ideal successor (axiom D).
    pub fn isDeonticSerial(self: *const MultiFrame) bool {
        var w: u32 = 0;
        while (w < self.n_worlds) : (w += 1) {
            if (self.deontic[w] == 0) return false;
        }
        return true;
    }
};

test "knows on reflexive singleton" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const kp = try arena.f(.{ .knows = .{ .agent = 0, .body = p } });

    var ep0 = [_]u32{0b1};
    var ep = [_][]u32{&ep0};
    var deo = [_]u32{0b1};
    var val = [_]u32{0b1};
    const frame = MultiFrame{
        .n_worlds = 1,
        .n_agents = 1,
        .epistemic = &ep,
        .deontic = &deo,
        .val = &val,
    };
    try std.testing.expect(frame.forces(0, kp));
    try std.testing.expect(frame.isDeonticSerial());
}

test "permitted vs obligatory" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const op = try arena.f(.{ .obligatory = p });
    const pp = try arena.f(.{ .permitted = p });

    // 2 worlds: 0 deontic-accesses only 1; p holds only at 1
    var ep0 = [_]u32{ 0b01, 0b10 };
    var ep = [_][]u32{&ep0};
    var deo = [_]u32{ 0b10, 0b10 }; // both see ideal world 1
    var val = [_]u32{0b10}; // p at world 1 only
    const frame = MultiFrame{
        .n_worlds = 2,
        .n_agents = 1,
        .epistemic = &ep,
        .deontic = &deo,
        .val = &val,
    };
    try std.testing.expect(frame.forces(0, op));
    try std.testing.expect(frame.forces(0, pp));
}
