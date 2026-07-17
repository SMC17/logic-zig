//! Combinational netlist IR + bit-blast to CNF + miter equivalence.
//!
//! Nets are dense IDs. Gates are multi-input AND/OR/XOR/NOT/MUX/CONST/BUF.
//! Suitable for Yosys JSON import of a small cell subset.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const NetId = enum(u32) {
    _,
    pub fn index(self: NetId) u32 {
        return @intFromEnum(self);
    }
    pub fn fromIndex(i: u32) NetId {
        return @enumFromInt(i);
    }
};

pub const GateKind = enum {
    @"const",
    buf,
    not,
    and_,
    or_,
    xor,
    xnor,
    nand,
    nor,
    mux,
    /// n-ary and/or of inputs → output
    and_n,
    or_n,
};

pub const Gate = struct {
    kind: GateKind,
    /// For const: 0 or 1 in inputs[0] as net unused; use const_val.
    const_val: bool = false,
    inputs: []const NetId,
    output: NetId,
};

/// Edge-triggered D latch / flop: next_q = d, current state is q.
pub const Latch = struct {
    d: NetId,
    q: NetId,
    /// Initial value of q at frame 0; null = unconstrained.
    init: ?bool = false,
};

pub const Netlist = struct {
    allocator: std.mem.Allocator,
    num_nets: u32 = 0,
    gates: std.ArrayList(Gate) = .empty,
    /// Primary inputs (combinational / per-frame free).
    inputs: std.ArrayList(NetId) = .empty,
    /// Primary outputs.
    outputs: std.ArrayList(NetId) = .empty,
    /// Sequential elements.
    latches: std.ArrayList(Latch) = .empty,
    /// HWMCC-style properties (extended AIGER).
    bad: std.ArrayList(NetId) = .empty,
    constraints: std.ArrayList(NetId) = .empty,
    justice: std.ArrayList(NetId) = .empty,
    fairness: std.ArrayList(NetId) = .empty,
    /// Optional names for nets.
    names: std.ArrayList(?[]const u8) = .empty,

    pub fn init(allocator: std.mem.Allocator) Netlist {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Netlist) void {
        for (self.gates.items) |g| {
            self.allocator.free(g.inputs);
        }
        self.gates.deinit(self.allocator);
        self.inputs.deinit(self.allocator);
        self.outputs.deinit(self.allocator);
        self.latches.deinit(self.allocator);
        self.bad.deinit(self.allocator);
        self.constraints.deinit(self.allocator);
        self.justice.deinit(self.allocator);
        self.fairness.deinit(self.allocator);
        for (self.names.items) |n| {
            if (n) |s| self.allocator.free(s);
        }
        self.names.deinit(self.allocator);
        self.* = undefined;
    }

    /// Bad properties: explicit list, or fall back to all outputs.
    pub fn badProps(self: *const Netlist) []const NetId {
        if (self.bad.items.len > 0) return self.bad.items;
        return self.outputs.items;
    }

    pub fn addBad(self: *Netlist, n: NetId) !void {
        try self.bad.append(self.allocator, n);
    }
    pub fn addConstraint(self: *Netlist, n: NetId) !void {
        try self.constraints.append(self.allocator, n);
    }
    pub fn addJustice(self: *Netlist, n: NetId) !void {
        try self.justice.append(self.allocator, n);
    }
    pub fn addFairness(self: *Netlist, n: NetId) !void {
        try self.fairness.append(self.allocator, n);
    }

    pub fn allocNet(self: *Netlist) !NetId {
        const id = NetId.fromIndex(self.num_nets);
        self.num_nets += 1;
        try self.names.append(self.allocator, null);
        return id;
    }

    pub fn allocNetNamed(self: *Netlist, name: []const u8) !NetId {
        const id = try self.allocNet();
        self.names.items[id.index()] = try self.allocator.dupe(u8, name);
        return id;
    }

    pub fn addInput(self: *Netlist, n: NetId) !void {
        try self.inputs.append(self.allocator, n);
    }

    pub fn addOutput(self: *Netlist, n: NetId) !void {
        try self.outputs.append(self.allocator, n);
    }

    pub fn addGate(self: *Netlist, kind: GateKind, inputs: []const NetId, output: NetId) !void {
        const owned = try self.allocator.dupe(NetId, inputs);
        try self.gates.append(self.allocator, .{
            .kind = kind,
            .inputs = owned,
            .output = output,
        });
    }

    pub fn addConst(self: *Netlist, output: NetId, val: bool) !void {
        try self.gates.append(self.allocator, .{
            .kind = .@"const",
            .const_val = val,
            .inputs = try self.allocator.alloc(NetId, 0),
            .output = output,
        });
    }

    pub fn addLatch(self: *Netlist, d: NetId, q: NetId, init_val: ?bool) !void {
        try self.latches.append(self.allocator, .{ .d = d, .q = q, .init = init_val });
    }

    /// Bit-blast: each net → SAT var with same index. Returns CNF of gate constraints.
    pub fn toCnf(self: *const Netlist, allocator: std.mem.Allocator) !Cnf {
        var cnf = Cnf.init(allocator);
        errdefer cnf.deinit();
        cnf.ensureVars(self.num_nets);

        for (self.gates.items) |g| {
            const y = Lit.positive(Var.fromIndex(g.output.index()));
            switch (g.kind) {
                .@"const" => {
                    if (g.const_val) try cnf.addClause(&.{y}) else try cnf.addClause(&.{y.not()});
                },
                .buf => {
                    const a = Lit.positive(Var.fromIndex(g.inputs[0].index()));
                    // y <-> a
                    try cnf.addClause(&.{ y.not(), a });
                    try cnf.addClause(&.{ a.not(), y });
                },
                .not => {
                    const a = Lit.positive(Var.fromIndex(g.inputs[0].index()));
                    // y <-> ~a
                    try cnf.addClause(&.{ y.not(), a.not() });
                    try cnf.addClause(&.{ a, y });
                },
                .and_, .and_n => {
                    // y -> each in; (all in) -> y
                    for (g.inputs) |inp| {
                        const a = Lit.positive(Var.fromIndex(inp.index()));
                        try cnf.addClause(&.{ y.not(), a });
                    }
                    var lits: std.ArrayList(Lit) = .empty;
                    defer lits.deinit(allocator);
                    for (g.inputs) |inp| {
                        try lits.append(allocator, Lit.negative(Var.fromIndex(inp.index())));
                    }
                    try lits.append(allocator, y);
                    try cnf.addClause(lits.items);
                },
                .or_, .or_n => {
                    for (g.inputs) |inp| {
                        const a = Lit.positive(Var.fromIndex(inp.index()));
                        try cnf.addClause(&.{ a.not(), y });
                    }
                    var lits: std.ArrayList(Lit) = .empty;
                    defer lits.deinit(allocator);
                    try lits.append(allocator, y.not());
                    for (g.inputs) |inp| {
                        try lits.append(allocator, Lit.positive(Var.fromIndex(inp.index())));
                    }
                    try cnf.addClause(lits.items);
                },
                .nand => {
                    for (g.inputs) |inp| {
                        try cnf.addClause(&.{ y, Lit.positive(Var.fromIndex(inp.index())) });
                    }
                    var lits: std.ArrayList(Lit) = .empty;
                    defer lits.deinit(allocator);
                    try lits.append(allocator, y.not());
                    for (g.inputs) |inp| try lits.append(allocator, Lit.negative(Var.fromIndex(inp.index())));
                    try cnf.addClause(lits.items);
                },
                .nor => {
                    for (g.inputs) |inp| {
                        try cnf.addClause(&.{ y.not(), Lit.negative(Var.fromIndex(inp.index())) });
                    }
                    var lits: std.ArrayList(Lit) = .empty;
                    defer lits.deinit(allocator);
                    for (g.inputs) |inp| try lits.append(allocator, Lit.positive(Var.fromIndex(inp.index())));
                    try lits.append(allocator, y);
                    try cnf.addClause(lits.items);
                },
                .xor => {
                    const a = Lit.positive(Var.fromIndex(g.inputs[0].index()));
                    const b = Lit.positive(Var.fromIndex(g.inputs[1].index()));
                    try cnf.addClause(&.{ y.not(), a, b });
                    try cnf.addClause(&.{ y.not(), a.not(), b.not() });
                    try cnf.addClause(&.{ y, a.not(), b });
                    try cnf.addClause(&.{ y, a, b.not() });
                },
                .xnor => {
                    const a = Lit.positive(Var.fromIndex(g.inputs[0].index()));
                    const b = Lit.positive(Var.fromIndex(g.inputs[1].index()));
                    try cnf.addClause(&.{ y, a, b });
                    try cnf.addClause(&.{ y, a.not(), b.not() });
                    try cnf.addClause(&.{ y.not(), a.not(), b });
                    try cnf.addClause(&.{ y.not(), a, b.not() });
                },
                .mux => {
                    const s = Lit.positive(Var.fromIndex(g.inputs[0].index()));
                    const t = Lit.positive(Var.fromIndex(g.inputs[1].index()));
                    const f = Lit.positive(Var.fromIndex(g.inputs[2].index()));
                    try cnf.addClause(&.{ s.not(), t.not(), y });
                    try cnf.addClause(&.{ s.not(), t, y.not() });
                    try cnf.addClause(&.{ s, f.not(), y });
                    try cnf.addClause(&.{ s, f, y.not() });
                },
            }
        }
        return cnf;
    }
};

pub const EquivResult = struct {
    equivalent: bool,
    /// Counterexample on shared inputs when not equivalent (owned).
    cex: ?[]Value = null,
    conflicts: u64 = 0,
};

/// Miter: share inputs, XOR each output pair, OR of XORs must be UNSAT for equivalence.
/// Requires same number of inputs/outputs. Nets of `a` and `b` are remapped into one CNF.
pub fn combinationalEquiv(
    allocator: std.mem.Allocator,
    a: *const Netlist,
    b: *const Netlist,
) !EquivResult {
    if (a.inputs.items.len != b.inputs.items.len) return error.PortMismatch;
    if (a.outputs.items.len != b.outputs.items.len) return error.PortMismatch;

    // Build unified net mapping: shared inputs first, then a-only nets, then b-only nets.
    // Simpler approach: encode each circuit with separate vars, equate inputs, miter outputs.
    var cnf = Cnf.init(allocator);
    defer cnf.deinit();

    const a_off: u32 = 0;
    const b_off: u32 = a.num_nets;
    cnf.ensureVars(a.num_nets + b.num_nets + @as(u32, @intCast(a.outputs.items.len)) + 1);

    // Helper to add gate CNF with offset.
    try blastWithOffset(allocator, &cnf, a, a_off);
    try blastWithOffset(allocator, &cnf, b, b_off);

    // Equate inputs: a.inputs[i] <-> b.inputs[i]
    for (a.inputs.items, b.inputs.items) |na, nb| {
        const la = Lit.positive(Var.fromIndex(a_off + na.index()));
        const lb = Lit.positive(Var.fromIndex(b_off + nb.index()));
        try cnf.addClause(&.{ la.not(), lb });
        try cnf.addClause(&.{ lb.not(), la });
    }

    // XOR outputs → miter bits, then OR them into miter_out.
    const miter_bits_start = a.num_nets + b.num_nets;
    var or_lits: std.ArrayList(Lit) = .empty;
    defer or_lits.deinit(allocator);

    for (a.outputs.items, b.outputs.items, 0..) |oa, ob, i| {
        const ya = Lit.positive(Var.fromIndex(a_off + oa.index()));
        const yb = Lit.positive(Var.fromIndex(b_off + ob.index()));
        const m = Lit.positive(Var.fromIndex(miter_bits_start + @as(u32, @intCast(i))));
        // m <-> ya xor yb
        try cnf.addClause(&.{ m.not(), ya, yb });
        try cnf.addClause(&.{ m.not(), ya.not(), yb.not() });
        try cnf.addClause(&.{ m, ya.not(), yb });
        try cnf.addClause(&.{ m, ya, yb.not() });
        try or_lits.append(allocator, m);
    }

    const miter_out = Lit.positive(Var.fromIndex(miter_bits_start + @as(u32, @intCast(a.outputs.items.len))));
    // miter_out <-> OR of miter bits
    if (or_lits.items.len == 0) {
        try cnf.addClause(&.{miter_out.not()}); // no outputs → equal
    } else {
        for (or_lits.items) |m| {
            try cnf.addClause(&.{ m.not(), miter_out });
        }
        var clause: std.ArrayList(Lit) = .empty;
        defer clause.deinit(allocator);
        try clause.append(allocator, miter_out.not());
        for (or_lits.items) |m| try clause.append(allocator, m);
        try cnf.addClause(clause.items);
    }
    // Force miter true → seek difference.
    try cnf.addClause(&.{miter_out});

    const r = try solver_mod.solveCnf(allocator, &cnf, .{});
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };

    if (r.status == .unsat) {
        return .{ .equivalent = true, .conflicts = r.conflicts };
    }
    if (r.status != .sat) {
        return .{ .equivalent = false, .conflicts = r.conflicts };
    }
    const full = r.model.?;
    defer allocator.free(full);

    // Extract input assignment from a side.
    const cex = try allocator.alloc(Value, a.inputs.items.len);
    for (a.inputs.items, 0..) |n, i| {
        cex[i] = full[a_off + n.index()];
    }
    return .{ .equivalent = false, .cex = cex, .conflicts = r.conflicts };
}

fn blastWithOffset(allocator: std.mem.Allocator, cnf: *Cnf, nl: *const Netlist, off: u32) !void {
    _ = allocator;
    for (nl.gates.items) |g| {
        const y = Lit.positive(Var.fromIndex(off + g.output.index()));
        switch (g.kind) {
            .@"const" => {
                if (g.const_val) try cnf.addClause(&.{y}) else try cnf.addClause(&.{y.not()});
            },
            .buf => {
                const a = Lit.positive(Var.fromIndex(off + g.inputs[0].index()));
                try cnf.addClause(&.{ y.not(), a });
                try cnf.addClause(&.{ a.not(), y });
            },
            .not => {
                const a = Lit.positive(Var.fromIndex(off + g.inputs[0].index()));
                try cnf.addClause(&.{ y.not(), a.not() });
                try cnf.addClause(&.{ a, y });
            },
            .and_, .and_n => {
                for (g.inputs) |inp| {
                    const a = Lit.positive(Var.fromIndex(off + inp.index()));
                    try cnf.addClause(&.{ y.not(), a });
                }
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(cnf.allocator);
                for (g.inputs) |inp| {
                    try lits.append(cnf.allocator, Lit.negative(Var.fromIndex(off + inp.index())));
                }
                try lits.append(cnf.allocator, y);
                try cnf.addClause(lits.items);
            },
            .or_, .or_n => {
                for (g.inputs) |inp| {
                    const a = Lit.positive(Var.fromIndex(off + inp.index()));
                    try cnf.addClause(&.{ a.not(), y });
                }
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(cnf.allocator);
                try lits.append(cnf.allocator, y.not());
                for (g.inputs) |inp| {
                    try lits.append(cnf.allocator, Lit.positive(Var.fromIndex(off + inp.index())));
                }
                try cnf.addClause(lits.items);
            },
            .nand => {
                for (g.inputs) |inp| try cnf.addClause(&.{ y, Lit.positive(Var.fromIndex(off + inp.index())) });
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(cnf.allocator);
                try lits.append(cnf.allocator, y.not());
                for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.negative(Var.fromIndex(off + inp.index())));
                try cnf.addClause(lits.items);
            },
            .nor => {
                for (g.inputs) |inp| try cnf.addClause(&.{ y.not(), Lit.negative(Var.fromIndex(off + inp.index())) });
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(cnf.allocator);
                for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.positive(Var.fromIndex(off + inp.index())));
                try lits.append(cnf.allocator, y);
                try cnf.addClause(lits.items);
            },
            .xor => {
                const a = Lit.positive(Var.fromIndex(off + g.inputs[0].index()));
                const b = Lit.positive(Var.fromIndex(off + g.inputs[1].index()));
                try cnf.addClause(&.{ y.not(), a, b });
                try cnf.addClause(&.{ y.not(), a.not(), b.not() });
                try cnf.addClause(&.{ y, a.not(), b });
                try cnf.addClause(&.{ y, a, b.not() });
            },
            .xnor => {
                const a = Lit.positive(Var.fromIndex(off + g.inputs[0].index()));
                const b = Lit.positive(Var.fromIndex(off + g.inputs[1].index()));
                try cnf.addClause(&.{ y, a, b });
                try cnf.addClause(&.{ y, a.not(), b.not() });
                try cnf.addClause(&.{ y.not(), a.not(), b });
                try cnf.addClause(&.{ y.not(), a, b.not() });
            },
            .mux => {
                const s = Lit.positive(Var.fromIndex(off + g.inputs[0].index()));
                const t = Lit.positive(Var.fromIndex(off + g.inputs[1].index()));
                const f = Lit.positive(Var.fromIndex(off + g.inputs[2].index()));
                try cnf.addClause(&.{ s.not(), t.not(), y });
                try cnf.addClause(&.{ s.not(), t, y.not() });
                try cnf.addClause(&.{ s, f.not(), y });
                try cnf.addClause(&.{ s, f, y.not() });
            },
        }
    }
}

test "half adder equiv self" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const sum = try nl.allocNetNamed("sum");
    const carry = try nl.allocNetNamed("carry");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.xor, &.{ a, b }, sum);
    try nl.addGate(.and_, &.{ a, b }, carry);
    try nl.addOutput(sum);
    try nl.addOutput(carry);

    const r = try combinationalEquiv(std.testing.allocator, &nl, &nl);
    defer if (r.cex) |c| std.testing.allocator.free(c);
    try std.testing.expect(r.equivalent);
}

test "half adder not equiv broken" {
    var good = Netlist.init(std.testing.allocator);
    defer good.deinit();
    const a = try good.allocNetNamed("a");
    const b = try good.allocNetNamed("b");
    const sum = try good.allocNetNamed("sum");
    try good.addInput(a);
    try good.addInput(b);
    try good.addGate(.xor, &.{ a, b }, sum);
    try good.addOutput(sum);

    var bad = Netlist.init(std.testing.allocator);
    defer bad.deinit();
    const a2 = try bad.allocNetNamed("a");
    const b2 = try bad.allocNetNamed("b");
    const sum2 = try bad.allocNetNamed("sum");
    try bad.addInput(a2);
    try bad.addInput(b2);
    try bad.addGate(.and_, &.{ a2, b2 }, sum2); // wrong
    try bad.addOutput(sum2);

    const r = try combinationalEquiv(std.testing.allocator, &good, &bad);
    defer if (r.cex) |c| std.testing.allocator.free(c);
    try std.testing.expect(!r.equivalent);
    try std.testing.expect(r.cex != null);
}
