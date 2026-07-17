//! Shared combinational gate → CNF blasting for sequential engines.
//! Keeps AND/OR/XOR/MUX/NAND/NOR/XNOR encodings consistent across BMC/PDR/justice.

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Netlist = netlist_mod.Netlist;
const Gate = netlist_mod.Gate;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub fn frameVar(num_nets: u32, frame: u32, net_index: u32) Var {
    return Var.fromIndex(frame * num_nets + net_index);
}

pub fn blastGate(cnf: *Cnf, g: Gate, frame: u32, nn: u32) !void {
    const y = Lit.positive(frameVar(nn, frame, g.output.index()));
    switch (g.kind) {
        .@"const" => {
            if (g.const_val) try cnf.addClause(&.{y}) else try cnf.addClause(&.{y.not()});
        },
        .buf => {
            const a = Lit.positive(frameVar(nn, frame, g.inputs[0].index()));
            try cnf.addClause(&.{ y.not(), a });
            try cnf.addClause(&.{ a.not(), y });
        },
        .not => {
            const a = Lit.positive(frameVar(nn, frame, g.inputs[0].index()));
            try cnf.addClause(&.{ y.not(), a.not() });
            try cnf.addClause(&.{ a, y });
        },
        .and_, .and_n => {
            for (g.inputs) |inp| {
                try cnf.addClause(&.{ y.not(), Lit.positive(frameVar(nn, frame, inp.index())) });
            }
            var lits: std.ArrayList(Lit) = .empty;
            defer lits.deinit(cnf.allocator);
            for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.negative(frameVar(nn, frame, inp.index())));
            try lits.append(cnf.allocator, y);
            try cnf.addClause(lits.items);
        },
        .nand => {
            // y ↔ ¬(a∧b) = ¬a ∨ ¬b
            for (g.inputs) |inp| {
                try cnf.addClause(&.{ y, Lit.positive(frameVar(nn, frame, inp.index())) });
            }
            var lits: std.ArrayList(Lit) = .empty;
            defer lits.deinit(cnf.allocator);
            try lits.append(cnf.allocator, y.not());
            for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.negative(frameVar(nn, frame, inp.index())));
            try cnf.addClause(lits.items);
        },
        .or_, .or_n => {
            for (g.inputs) |inp| {
                try cnf.addClause(&.{ Lit.negative(frameVar(nn, frame, inp.index())), y });
            }
            var lits: std.ArrayList(Lit) = .empty;
            defer lits.deinit(cnf.allocator);
            try lits.append(cnf.allocator, y.not());
            for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.positive(frameVar(nn, frame, inp.index())));
            try cnf.addClause(lits.items);
        },
        .nor => {
            // y ↔ ¬(a∨b) = ¬a ∧ ¬b
            for (g.inputs) |inp| {
                try cnf.addClause(&.{ y.not(), Lit.negative(frameVar(nn, frame, inp.index())) });
            }
            var lits: std.ArrayList(Lit) = .empty;
            defer lits.deinit(cnf.allocator);
            for (g.inputs) |inp| try lits.append(cnf.allocator, Lit.positive(frameVar(nn, frame, inp.index())));
            try lits.append(cnf.allocator, y);
            try cnf.addClause(lits.items);
        },
        .xor => {
            const a = Lit.positive(frameVar(nn, frame, g.inputs[0].index()));
            const b = Lit.positive(frameVar(nn, frame, g.inputs[1].index()));
            try cnf.addClause(&.{ y.not(), a, b });
            try cnf.addClause(&.{ y.not(), a.not(), b.not() });
            try cnf.addClause(&.{ y, a.not(), b });
            try cnf.addClause(&.{ y, a, b.not() });
        },
        .xnor => {
            const a = Lit.positive(frameVar(nn, frame, g.inputs[0].index()));
            const b = Lit.positive(frameVar(nn, frame, g.inputs[1].index()));
            // y ↔ a xnor b ≡ ¬(a xor b)
            try cnf.addClause(&.{ y, a, b });
            try cnf.addClause(&.{ y, a.not(), b.not() });
            try cnf.addClause(&.{ y.not(), a.not(), b });
            try cnf.addClause(&.{ y.not(), a, b.not() });
        },
        .mux => {
            const s = Lit.positive(frameVar(nn, frame, g.inputs[0].index()));
            const t = Lit.positive(frameVar(nn, frame, g.inputs[1].index()));
            const f = Lit.positive(frameVar(nn, frame, g.inputs[2].index()));
            try cnf.addClause(&.{ s.not(), t.not(), y });
            try cnf.addClause(&.{ s.not(), t, y.not() });
            try cnf.addClause(&.{ s, f.not(), y });
            try cnf.addClause(&.{ s, f, y.not() });
        },
    }
}

pub fn blastFrame(cnf: *Cnf, nl: *const Netlist, frame: u32) !void {
    const nn = nl.num_nets;
    for (nl.gates.items) |g| try blastGate(cnf, g, frame, nn);
}

pub fn blastFrameNn(cnf: *Cnf, nl: *const Netlist, frame: u32, nn: u32) !void {
    for (nl.gates.items) |g| try blastGate(cnf, g, frame, nn);
}
