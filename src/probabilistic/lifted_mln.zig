//! Lifted Markov logic — first-order weighted formulas + grounding.
//!
//! A lifted MLN formula has free variables ranging over a finite domain.
//! Grounding enumerates all domain assignments and produces a propositional
//! MLN (`markov.zig`) whose atoms are predicate applications P(c1,…,ck).
//!
//! Fragment: unary/binary predicates, domain size ≤ 4, ≤ 3 predicates,
//! exhaustive grounding (not knowledge-based model construction / WPLL).

const std = @import("std");
const markov = @import("markov.zig");
const prob = @import("prob.zig");

pub const PredId = u32;
pub const ConstId = u32;
pub const VarId = u32;

pub const Atom = struct {
    pred: PredId,
    /// Args are variables (lifted) — constants after grounding via substitution.
    args: []const VarId,
};

pub const LiftedFormula = union(enum) {
    atom: Atom,
    not: *LiftedFormula,
    and_: struct { l: *LiftedFormula, r: *LiftedFormula },
    or_: struct { l: *LiftedFormula, r: *LiftedFormula },
};

pub const WeightedLifted = struct {
    weight: f64,
    formula: *LiftedFormula,
    /// Number of free variables (domain^arity groundings).
    n_vars: u32,
};

pub const LiftedMLN = struct {
    formulas: []const WeightedLifted,
    /// Predicate arities.
    pred_arities: []const u32,
    domain_size: u32,
};

pub const Arena = struct {
    allocator: std.mem.Allocator,
    nodes: std.ArrayList(*LiftedFormula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Arena {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Arena) void {
        for (self.nodes.items) |n| self.allocator.destroy(n);
        self.nodes.deinit(self.allocator);
        self.* = undefined;
    }
    pub fn f(self: *Arena, v: LiftedFormula) !*LiftedFormula {
        const p = try self.allocator.create(LiftedFormula);
        p.* = v;
        try self.nodes.append(self.allocator, p);
        return p;
    }
};

/// Map (pred, c0, c1, …) → propositional atom index.
fn groundAtomIndex(pred: PredId, args: []const ConstId, pred_arities: []const u32, domain: u32) u32 {
    var idx: u32 = 0;
    var p: u32 = 0;
    while (p < pred) : (p += 1) {
        var space: u32 = 1;
        var a: u32 = 0;
        while (a < pred_arities[p]) : (a += 1) space *= domain;
        idx += space;
    }
    // mixed-radix encode args
    var offset: u32 = 0;
    var place: u32 = 1;
    var i: usize = 0;
    while (i < args.len) : (i += 1) {
        offset += args[i] * place;
        place *= domain;
    }
    return idx + offset;
}

pub fn nGroundAtoms(pred_arities: []const u32, domain: u32) u32 {
    var n: u32 = 0;
    for (pred_arities) |ar| {
        var space: u32 = 1;
        var a: u32 = 0;
        while (a < ar) : (a += 1) space *= domain;
        n += space;
    }
    return n;
}

fn substFormula(
    arena: *prob.Arena,
    phi: *const LiftedFormula,
    assignment: []const ConstId,
    pred_arities: []const u32,
    domain: u32,
) !*prob.Formula {
    return switch (phi.*) {
        .atom => |at| blk: {
            var consts: [4]ConstId = undefined;
            for (at.args, 0..) |v, i| consts[i] = assignment[v];
            const idx = groundAtomIndex(at.pred, consts[0..at.args.len], pred_arities, domain);
            break :blk try arena.f(.{ .atom = idx });
        },
        .not => |n| try arena.f(.{ .not = try substFormula(arena, n, assignment, pred_arities, domain) }),
        .and_ => |a| try arena.f(.{
            .and_ = .{
                .l = try substFormula(arena, a.l, assignment, pred_arities, domain),
                .r = try substFormula(arena, a.r, assignment, pred_arities, domain),
            },
        }),
        .or_ => |a| try arena.f(.{
            .or_ = .{
                .l = try substFormula(arena, a.l, assignment, pred_arities, domain),
                .r = try substFormula(arena, a.r, assignment, pred_arities, domain),
            },
        }),
    };
}

pub const Grounded = struct {
    mln: markov.MLN,
    weighted: []markov.WeightedFormula,
    prop_arena: prob.Arena,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *Grounded) void {
        self.allocator.free(self.weighted);
        self.prop_arena.deinit();
        self.* = undefined;
    }
};

/// Exhaustive grounding of a lifted MLN into a propositional MLN.
pub fn ground(allocator: std.mem.Allocator, lifted: *const LiftedMLN) !Grounded {
    if (lifted.domain_size > 4) return error.DomainTooLarge;
    var prop_arena = prob.Arena.init(allocator);
    errdefer prop_arena.deinit();

    var wlist: std.ArrayList(markov.WeightedFormula) = .empty;
    errdefer wlist.deinit(allocator);

    for (lifted.formulas) |wf| {
        const nv = wf.n_vars;
        if (nv > 4) return error.DomainTooLarge;
        const full: u32 = if (nv == 0) 1 else blk: {
            var s: u32 = 1;
            var i: u32 = 0;
            while (i < nv) : (i += 1) s *= lifted.domain_size;
            break :blk s;
        };
        var g: u32 = 0;
        while (g < full) : (g += 1) {
            var assignment: [4]ConstId = .{ 0, 0, 0, 0 };
            var tmp = g;
            var v: u32 = 0;
            while (v < nv) : (v += 1) {
                assignment[v] = tmp % lifted.domain_size;
                tmp /= lifted.domain_size;
            }
            const pf = try substFormula(&prop_arena, wf.formula, assignment[0..nv], lifted.pred_arities, lifted.domain_size);
            try wlist.append(allocator, .{ .weight = wf.weight, .formula = pf });
        }
    }

    const slice = try wlist.toOwnedSlice(allocator);
    const n_atoms = nGroundAtoms(lifted.pred_arities, lifted.domain_size);
    return .{
        .mln = .{ .formulas = slice, .n_atoms = n_atoms },
        .weighted = slice,
        .prop_arena = prop_arena,
        .allocator = allocator,
    };
}

test "unary predicate grounding size" {
    // One unary pred P, domain 2 → 2 ground atoms
    try std.testing.expect(nGroundAtoms(&[_]u32{1}, 2) == 2);
}

test "lifted soft fact raises marginal" {
    var arena = Arena.init(std.testing.allocator);
    defer arena.deinit();
    // P(x) weight 5, domain {0,1}
    const args = [_]VarId{0};
    const atom = try arena.f(.{ .atom = .{ .pred = 0, .args = &args } });
    const wf = WeightedLifted{ .weight = 5, .formula = atom, .n_vars = 1 };
    const lifted = LiftedMLN{
        .formulas = &[_]WeightedLifted{wf},
        .pred_arities = &[_]u32{1},
        .domain_size = 2,
    };
    var g = try ground(std.testing.allocator, &lifted);
    defer g.deinit();
    try std.testing.expect(g.mln.n_atoms == 2);
    try std.testing.expect(g.mln.formulas.len == 2); // one per domain element
    const m0 = markov.marginal(&g.mln, 0);
    try std.testing.expect(m0 > 0.5);
}
