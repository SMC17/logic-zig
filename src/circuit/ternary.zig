//! 3-valued (ternary) simulation for netlists: 0 / 1 / X.
//!
//! Used for:
//! - Fast combinational evaluation under partial assignments
//! - PDR cube weakening: drop latch lits that remain X while property still 1
//! - X-propagation diagnostics
//!
//! Semantics (Kleene):
//!   NOT:  ~0=1, ~1=0, ~X=X
//!   AND:  min (0 < X < 1) with 0 absorbing
//!   OR:   max
//!   XOR:  inequality, X if either X
//!   MUX:  s=0→f, s=1→t, s=X→X unless t==f

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const GateKind = netlist_mod.GateKind;

pub const Tri = enum(u2) {
    zero = 0,
    one = 1,
    x = 2,

    pub fn fromBool(b: bool) Tri {
        return if (b) .one else .zero;
    }

    pub fn toBool(self: Tri) ?bool {
        return switch (self) {
            .zero => false,
            .one => true,
            .x => null,
        };
    }

    pub fn not(self: Tri) Tri {
        return switch (self) {
            .zero => .one,
            .one => .zero,
            .x => .x,
        };
    }

    pub fn bitAnd(a: Tri, b: Tri) Tri {
        if (a == .zero or b == .zero) return .zero;
        if (a == .one and b == .one) return .one;
        return .x;
    }

    pub fn bitOr(a: Tri, b: Tri) Tri {
        if (a == .one or b == .one) return .one;
        if (a == .zero and b == .zero) return .zero;
        return .x;
    }

    pub fn bitXor(a: Tri, b: Tri) Tri {
        if (a == .x or b == .x) return .x;
        return if (a != b) .one else .zero;
    }

    pub fn mux(s: Tri, t: Tri, f: Tri) Tri {
        return switch (s) {
            .zero => f,
            .one => t,
            .x => if (t == f and t != .x) t else .x,
        };
    }
};

pub const SimState = struct {
    allocator: std.mem.Allocator,
    values: []Tri,
    /// Gate evaluation order (topological indices into gates array).
    order: []usize,

    pub fn init(allocator: std.mem.Allocator, nl: *const Netlist) !SimState {
        const values = try allocator.alloc(Tri, nl.num_nets);
        @memset(values, .x);
        const order = try topoOrder(allocator, nl);
        return .{ .allocator = allocator, .values = values, .order = order };
    }

    pub fn deinit(self: *SimState) void {
        self.allocator.free(self.values);
        self.allocator.free(self.order);
        self.* = undefined;
    }

    pub fn set(self: *SimState, n: NetId, v: Tri) void {
        self.values[n.index()] = v;
    }

    pub fn get(self: *const SimState, n: NetId) Tri {
        return self.values[n.index()];
    }

    pub fn resetX(self: *SimState) void {
        @memset(self.values, .x);
    }

    /// Evaluate all combinational gates in topo order (latches are state: q not driven by gates).
    pub fn evalComb(self: *SimState, nl: *const Netlist) void {
        // Drive constants first
        for (nl.gates.items) |g| {
            if (g.kind == .@"const") {
                self.values[g.output.index()] = Tri.fromBool(g.const_val);
            }
        }
        for (self.order) |gi| {
            const g = nl.gates.items[gi];
            self.values[g.output.index()] = evalGate(g, self.values);
        }
    }

    /// Set latch q from assignment map (partial → X for missing).
    pub fn setLatches(self: *SimState, nl: *const Netlist, latch_vals: []const Tri) void {
        std.debug.assert(latch_vals.len == nl.latches.items.len);
        for (nl.latches.items, 0..) |lat, i| {
            self.values[lat.q.index()] = latch_vals[i];
        }
    }

    /// After comb eval, read next-state d for each latch.
    pub fn nextLatchVals(self: *const SimState, nl: *const Netlist, out: []Tri) void {
        std.debug.assert(out.len == nl.latches.items.len);
        for (nl.latches.items, 0..) |lat, i| {
            out[i] = self.values[lat.d.index()];
        }
    }
};

fn evalGate(g: netlist_mod.Gate, vals: []const Tri) Tri {
    return switch (g.kind) {
        .@"const" => Tri.fromBool(g.const_val),
        .buf => vals[g.inputs[0].index()],
        .not => vals[g.inputs[0].index()].not(),
        .and_, .and_n => blk: {
            var acc: Tri = .one;
            for (g.inputs) |inp| acc = Tri.bitAnd(acc, vals[inp.index()]);
            break :blk acc;
        },
        .nand => blk: {
            var acc: Tri = .one;
            for (g.inputs) |inp| acc = Tri.bitAnd(acc, vals[inp.index()]);
            break :blk acc.not();
        },
        .or_, .or_n => blk: {
            var acc: Tri = .zero;
            for (g.inputs) |inp| acc = Tri.bitOr(acc, vals[inp.index()]);
            break :blk acc;
        },
        .nor => blk: {
            var acc: Tri = .zero;
            for (g.inputs) |inp| acc = Tri.bitOr(acc, vals[inp.index()]);
            break :blk acc.not();
        },
        .xor => Tri.bitXor(vals[g.inputs[0].index()], vals[g.inputs[1].index()]),
        .xnor => Tri.bitXor(vals[g.inputs[0].index()], vals[g.inputs[1].index()]).not(),
        .mux => Tri.mux(
            vals[g.inputs[0].index()],
            vals[g.inputs[1].index()],
            vals[g.inputs[2].index()],
        ),
    };
}

fn topoOrder(allocator: std.mem.Allocator, nl: *const Netlist) ![]usize {
    const ng = nl.gates.items.len;
    var indeg = try allocator.alloc(u32, ng);
    defer allocator.free(indeg);
    @memset(indeg, 0);

    var producer = try allocator.alloc(?usize, nl.num_nets);
    defer allocator.free(producer);
    @memset(producer, null);
    for (nl.gates.items, 0..) |g, gi| producer[g.output.index()] = gi;

    var adj = try allocator.alloc(std.ArrayList(usize), ng);
    defer {
        for (adj) |*a| a.deinit(allocator);
        allocator.free(adj);
    }
    for (adj) |*a| a.* = .empty;

    for (nl.gates.items, 0..) |g, gi| {
        for (g.inputs) |inp| {
            if (producer[inp.index()]) |pg| {
                try adj[pg].append(allocator, gi);
                indeg[gi] += 1;
            }
        }
    }

    var order: std.ArrayList(usize) = .empty;
    errdefer order.deinit(allocator);
    var queue: std.ArrayList(usize) = .empty;
    defer queue.deinit(allocator);
    for (indeg, 0..) |d, gi| {
        if (d == 0) try queue.append(allocator, gi);
    }
    var qh: usize = 0;
    while (qh < queue.items.len) : (qh += 1) {
        const u = queue.items[qh];
        try order.append(allocator, u);
        for (adj[u].items) |v| {
            indeg[v] -= 1;
            if (indeg[v] == 0) try queue.append(allocator, v);
        }
    }
    if (order.items.len < ng) {
        for (0..ng) |gi| {
            var found = false;
            for (order.items) |o| {
                if (o == gi) {
                    found = true;
                    break;
                }
            }
            if (!found) try order.append(allocator, gi);
        }
    }
    return try order.toOwnedSlice(allocator);
}

/// Ternary-guided cube weakening for a property net that should stay 1 under cube.
/// Starts from full latch cube (as 0/1), sets each latch to X if property still evaluates to 1.
pub fn weakenCubeForProperty(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    prop: NetId,
    /// One Tri per latch (must be 0/1, not X)
    latch_cube: []const Tri,
) ![]Tri {
    var sim = try SimState.init(allocator, nl);
    defer sim.deinit();
    var weakened = try allocator.dupe(Tri, latch_cube);
    errdefer allocator.free(weakened);

    // Inputs stay X (existential)
    var i: usize = 0;
    while (i < weakened.len) : (i += 1) {
        const saved = weakened[i];
        weakened[i] = .x;
        sim.resetX();
        sim.setLatches(nl, weakened);
        // free inputs remain X
        sim.evalComb(nl);
        if (sim.get(prop) != .one) {
            weakened[i] = saved; // needed
        }
    }
    return weakened;
}

/// Evaluate one frame: latches + optional inputs → comb (and next via `nextLatchVals`).
pub fn evalFrame(
    sim: *SimState,
    nl: *const Netlist,
    latch_vals: []const Tri,
    input_vals: ?[]const Tri,
) void {
    sim.resetX();
    sim.setLatches(nl, latch_vals);
    if (input_vals) |iv| {
        std.debug.assert(iv.len == nl.inputs.items.len);
        for (nl.inputs.items, 0..) |inp, i| sim.set(inp, iv[i]);
    }
    sim.evalComb(nl);
}

/// Sequential ternary step: latch_vals → next latch values (inputs free = X).
pub fn step(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    latch_vals: []const Tri,
    input_vals: ?[]const Tri,
    next_out: []Tri,
) !void {
    var sim = try SimState.init(allocator, nl);
    defer sim.deinit();
    evalFrame(&sim, nl, latch_vals, input_vals);
    sim.nextLatchVals(nl, next_out);
}

/// Multi-round ternary weaken: drop latch lits while prop stays 1 AND next-state
/// still compatible with a target next cube (optional, for inductive gen).
pub fn weakenCubeInductive(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    prop: NetId,
    latch_cube: []const Tri,
    /// If non-null, next-state under free inputs must not contradict these (0/1 only).
    next_must: ?[]const Tri,
) ![]Tri {
    var sim = try SimState.init(allocator, nl);
    defer sim.deinit();
    var weakened = try allocator.dupe(Tri, latch_cube);
    errdefer allocator.free(weakened);
    const next_buf = try allocator.alloc(Tri, nl.latches.items.len);
    defer allocator.free(next_buf);

    var i: usize = 0;
    while (i < weakened.len) : (i += 1) {
        const saved = weakened[i];
        weakened[i] = .x;
        evalFrame(&sim, nl, weakened, null);
        if (sim.get(prop) != .one) {
            weakened[i] = saved;
            continue;
        }
        if (next_must) |nm| {
            sim.nextLatchVals(nl, next_buf);
            var ok = true;
            for (nm, next_buf) |need, got| {
                if (need == .x) continue;
                if (got != .x and got != need) {
                    ok = false;
                    break;
                }
            }
            if (!ok) weakened[i] = saved;
        }
    }
    return weakened;
}

test "tri ops" {
    try std.testing.expect(Tri.bitAnd(.one, .one) == .one);
    try std.testing.expect(Tri.bitAnd(.one, .x) == .x);
    try std.testing.expect(Tri.bitAnd(.zero, .x) == .zero);
    try std.testing.expect(Tri.bitOr(.zero, .x) == .x);
    try std.testing.expect(Tri.mux(.x, .one, .one) == .one);
    try std.testing.expect(Tri.mux(.x, .one, .zero) == .x);
}

test "ternary and gate" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.and_, &.{ a, b }, y);
    try nl.addOutput(y);

    var sim = try SimState.init(std.testing.allocator, &nl);
    defer sim.deinit();
    sim.set(a, .one);
    sim.set(b, .x);
    sim.evalComb(&nl);
    try std.testing.expect(sim.get(y) == .x);
    sim.set(b, .zero);
    sim.evalComb(&nl);
    try std.testing.expect(sim.get(y) == .zero);
}

test "weaken cube keeps necessary lit" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    // prop = q0 (latch), so cube must keep q0=1
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, true);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);

    const cube = [_]Tri{.one};
    const w = try weakenCubeForProperty(std.testing.allocator, &nl, q, &cube);
    defer std.testing.allocator.free(w);
    // q is prop itself — setting to X makes prop X, so must keep one
    try std.testing.expect(w[0] == .one);
}

test "ternary step toggle" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    var next: [1]Tri = undefined;
    try step(std.testing.allocator, &nl, &[_]Tri{.zero}, null, &next);
    try std.testing.expect(next[0] == .one);
    try step(std.testing.allocator, &nl, &[_]Tri{.one}, null, &next);
    try std.testing.expect(next[0] == .zero);
}

test "weakenCubeInductive drops free lit" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    // prop = q0; q1 is free for property
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    try nl.addConst(d0, false);
    try nl.addConst(d1, false);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    const cube = [_]Tri{ .one, .one };
    const w = try weakenCubeInductive(std.testing.allocator, &nl, q0, &cube, null);
    defer std.testing.allocator.free(w);
    try std.testing.expect(w[0] == .one);
    try std.testing.expect(w[1] == .x);
}
