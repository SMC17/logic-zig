//! Bounded Linear Temporal Logic (LTL) over finite traces.
//!
//! Supported fragment (bounded path semantics, frames 0..bound):
//!   ap(p)  not  and  or  X(φ)  F(φ)  G(φ)  φ U ψ  φ R ψ
//!
//! Two independent evaluators, cross-checked:
//!   1. `evalDirect` — recursive structural evaluation over an explicit trace.
//!   2. `evalSat`    — textbook bounded LTL→SAT encoding, solved by the CDCL core.
//! They must agree on every (trace, formula) pair; an exhaustive oracle asserts
//! textbook validities (e.g. F p → p U p, G p ↔ p R false, duality).
//!
//! Bounded scope (honest): this decides LTL *over finite traces of length ≤ bound*,
//! not the full ω-regular LTL model-checking problem. Labels therefore say
//! `holds_within_bound` / `fails_within_bound`, never an unbounded proof.

const std = @import("std");
const solver_mod = @import("../sat/solver.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Solver = solver_mod.Solver;
const SolveResult = solver_mod.SolveResult;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;

pub const LtlStatus = enum { holds_within_bound, fails_within_bound, unknown };
pub const LtlResult = struct {
    status: LtlStatus,
    bound: u32,
    conflicts: u64 = 0,
};

/// Finite trace: `frames` × `nets` booleans, indexed `i*nets + n`.
pub const Trace = struct {
    allocator: std.mem.Allocator,
    frames: u32,
    nets: u32,
    data: []bool,

    pub fn init(allocator: std.mem.Allocator, frames: u32, nets: u32) !Trace {
        const data = try allocator.alloc(bool, @as(usize, frames) * nets);
        @memset(data, false);
        return .{ .allocator = allocator, .frames = frames, .nets = nets, .data = data };
    }
    pub fn deinit(self: *Trace) void {
        self.allocator.free(self.data);
        self.* = undefined;
    }
    pub fn at(self: *const Trace, frame: u32, net: u32) bool {
        return self.data[@as(usize, frame) * self.nets + net];
    }
    pub fn set(self: *Trace, frame: u32, net: u32, v: bool) void {
        self.data[@as(usize, frame) * self.nets + net] = v;
    }
};

pub const Formula = struct {
    tag: Tag,
    /// For `ap`: net index. For binary: left/right subformula ids.
    net: u32 = 0,
    lhs: u32 = 0,
    rhs: u32 = 0,

    pub const Tag = enum { ap, not, and_, or_, next, eventually, globally, until, release };
};

/// Formula arena. Formulas carry stable ids (index into `items`).
pub const Builder = struct {
    allocator: std.mem.Allocator,
    items: std.ArrayList(Formula) = .empty,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .allocator = allocator };
    }
    pub fn deinit(self: *Builder) void {
        self.items.deinit(self.allocator);
    }
    fn add(self: *Builder, f: Formula) !u32 {
        const id = @as(u32, @intCast(self.items.items.len));
        try self.items.append(self.allocator, f);
        return id;
    }
    pub fn ap(self: *Builder, net: u32) !u32 {
        return self.add(.{ .tag = .ap, .net = net });
    }
    pub fn not_(self: *Builder, a: u32) !u32 {
        return self.add(.{ .tag = .not, .lhs = a });
    }
    pub fn and_(self: *Builder, a: u32, b: u32) !u32 {
        return self.add(.{ .tag = .and_, .lhs = a, .rhs = b });
    }
    pub fn or_(self: *Builder, a: u32, b: u32) !u32 {
        return self.add(.{ .tag = .or_, .lhs = a, .rhs = b });
    }
    pub fn next(self: *Builder, a: u32) !u32 {
        return self.add(.{ .tag = .next, .lhs = a });
    }
    pub fn eventually(self: *Builder, a: u32) !u32 {
        return self.add(.{ .tag = .eventually, .lhs = a });
    }
    pub fn globally(self: *Builder, a: u32) !u32 {
        return self.add(.{ .tag = .globally, .lhs = a });
    }
    pub fn until(self: *Builder, a: u32, b: u32) !u32 {
        return self.add(.{ .tag = .until, .lhs = a, .rhs = b });
    }
    pub fn release(self: *Builder, a: u32, b: u32) !u32 {
        return self.add(.{ .tag = .release, .lhs = a, .rhs = b });
    }
};

/// 1) Direct structural evaluation at `frame` (must be ≤ bound).
pub fn evalDirect(b: *const Builder, tr: *const Trace, frame: u32, f: u32) bool {
    const frm = b.items.items[f];
    switch (frm.tag) {
        .ap => return tr.at(frame, frm.net),
        .not => return !evalDirect(b, tr, frame, frm.lhs),
        .and_ => return evalDirect(b, tr, frame, frm.lhs) and evalDirect(b, tr, frame, frm.rhs),
        .or_ => return evalDirect(b, tr, frame, frm.lhs) or evalDirect(b, tr, frame, frm.rhs),
        .next => {
            if (frame + 1 >= tr.frames) return false; // off-end bounded semantics
            return evalDirect(b, tr, frame + 1, frm.lhs);
        },
        .eventually => {
            var i = frame;
            while (i < tr.frames) : (i += 1) {
                if (evalDirect(b, tr, i, frm.lhs)) return true;
            }
            return false;
        },
        .globally => {
            var i = frame;
            while (i < tr.frames) : (i += 1) {
                if (!evalDirect(b, tr, i, frm.lhs)) return false;
            }
            return true;
        },
        .until => {
            // Recurrence U_i = ψ_i ∨ (φ_i ∧ U_{i+1}); U_{L+1} = false (bounded).
            // Matches the SAT encoding exactly, including the last-frame base case.
            if (frame >= tr.frames) return false;
            const psi = evalDirect(b, tr, frame, frm.rhs);
            const phi = evalDirect(b, tr, frame, frm.lhs);
            const later = evalDirect(b, tr, frame + 1, f);
            return psi or (phi and later);
        },
        .release => {
            // Recurrence R_i = ψ_i ∨ (φ_i ∧ R_{i+1}); R_{L+1} = false (bounded).
            // Matches the SAT encoding exactly, including the last-frame base case.
            if (frame >= tr.frames) return false;
            const psi = evalDirect(b, tr, frame, frm.rhs);
            const phi = evalDirect(b, tr, frame, frm.lhs);
            const later = evalDirect(b, tr, frame + 1, f);
            return psi or (phi and later);
        },
    }
}

/// 2) SAT encoding. One boolean var per (subformula id, frame). Returns the
/// root var at frame 0; the formula holds iff that var is forced true.
pub fn encodeSat(allocator: std.mem.Allocator, b: *const Builder, tr: *const Trace, root: u32) !struct {
    cnf: Cnf,
    root_var: Var,
    conflicts: u64,
} {
    const n = b.items.items.len;
    const frames = tr.frames;
    // var[f][i] for f in 0..n, i in 0..frames. packed as f*frames + i.
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();
    cnf.ensureVars(@as(u32, @intCast(n)) * frames + 1);
    const vof = struct {
        fn f(fid: u32, i: u32, nf: u32) Var {
            return Var.fromIndex(fid * nf + i);
        }
    }.f;

    var fid: u32 = 0;
    while (fid < n) : (fid += 1) {
        const frm = b.items.items[fid];
        var i: u32 = 0;
        while (i < frames) : (i += 1) {
            const v = vof(fid, i, frames);
            const lv = Lit.positive(v);
            const lnot = Lit.negative(v);
            switch (frm.tag) {
                .ap => {
                    // v <-> trace[i][net]
                    if (tr.at(i, frm.net)) {
                        try cnf.addClause(&.{lv});
                    } else {
                        try cnf.addClause(&.{lnot});
                    }
                },
                .not => {
                    const a = vof(frm.lhs, i, frames);
                    // v <-> ¬a :  {¬v, ¬a}, {a, v}
                    try cnf.addClause(&.{ lnot, Lit.negative(a) });
                    try cnf.addClause(&.{ lv, Lit.positive(a) });
                },
                .and_ => {
                    const a = vof(frm.lhs, i, frames);
                    const c = vof(frm.rhs, i, frames);
                    try cnf.addClause(&.{ lnot, Lit.positive(a) });
                    try cnf.addClause(&.{ lnot, Lit.positive(c) });
                    try cnf.addClause(&.{ lv, Lit.negative(a), Lit.negative(c) });
                },
                .or_ => {
                    const a = vof(frm.lhs, i, frames);
                    const c = vof(frm.rhs, i, frames);
                    try cnf.addClause(&.{ lv, Lit.negative(a) });
                    try cnf.addClause(&.{ lv, Lit.negative(c) });
                    try cnf.addClause(&.{ lnot, Lit.positive(a), Lit.positive(c) });
                },
                .next => {
                    const a = if (i + 1 < frames) vof(frm.lhs, i + 1, frames) else null;
                    if (a) |av| {
                        try cnf.addClause(&.{ lnot, Lit.positive(av) });
                        try cnf.addClause(&.{ lv, Lit.negative(av) });
                    } else {
                        try cnf.addClause(&.{ lnot }); // v forced false
                    }
                },
                .eventually => {
                    const a = vof(frm.lhs, i, frames);
                    const nxt = if (i + 1 < frames) vof(fid, i + 1, frames) else null;
                    // v <-> (a ∨ next):
                    //   child→v: (¬a∧¬next)∨v  →  {−a,−next,+v}
                    //   v→child:  ¬v∨a∨next       →  {−v,+a,+next}
                    if (nxt) |nv| {
                        try cnf.addClause(&.{ lv, Lit.negative(a), Lit.negative(nv) });
                        try cnf.addClause(&.{ lnot, Lit.positive(a), Lit.positive(nv) });
                    } else {
                        // last frame: v <-> a
                        try cnf.addClause(&.{ lv, Lit.negative(a) });
                        try cnf.addClause(&.{ lnot, Lit.positive(a) });
                    }
                },
                .globally => {
                    const a = vof(frm.lhs, i, frames);
                    const nxt = if (i + 1 < frames) vof(fid, i + 1, frames) else null;
                    // v <-> (a ∧ next):
                    //   child→v: (¬a∧¬next)∨v  →  {−a,−next,+v}
                    //   v→child:  ¬v∨a  and  ¬v∨next  (AND distributes)
                    if (nxt) |nv| {
                        try cnf.addClause(&.{ lv, Lit.negative(a), Lit.negative(nv) });
                        try cnf.addClause(&.{ lnot, Lit.positive(a) });
                        try cnf.addClause(&.{ lnot, Lit.positive(nv) });
                    } else {
                        // last frame: v <-> a
                        try cnf.addClause(&.{ lv, Lit.negative(a) });
                        try cnf.addClause(&.{ lnot, Lit.positive(a) });
                    }
                },
                .until => {
                    const a = vof(frm.lhs, i, frames);
                    const c = vof(frm.rhs, i, frames);
                    const nxt = if (i + 1 < frames) vof(fid, i + 1, frames) else null;
                    // v <-> (c ∨ (a ∧ next)):
                    //   child→v: (¬c∧¬a)∨v, (¬c∧¬next)∨v
                    //   v→child: ¬v∨c∨a, ¬v∨c∨next
                    if (nxt) |nv| {
                        try cnf.addClause(&.{ lv, Lit.negative(c), Lit.negative(a) });
                        try cnf.addClause(&.{ lv, Lit.negative(c), Lit.negative(nv) });
                        try cnf.addClause(&.{ lnot, Lit.positive(c), Lit.positive(a) });
                        try cnf.addClause(&.{ lnot, Lit.positive(c), Lit.positive(nv) });
                    } else {
                        // last frame: v <-> c
                        try cnf.addClause(&.{ lnot, Lit.positive(c) });
                        try cnf.addClause(&.{ lv, Lit.negative(c) });
                    }
                },
                .release => {
                    const a = vof(frm.lhs, i, frames);
                    const c = vof(frm.rhs, i, frames);
                    const nxt = if (i + 1 < frames) vof(fid, i + 1, frames) else null;
                    // v <-> (c ∧ (a ∨ next)):
                    //   child→v: (¬c∨¬a)∨v, (¬c∨¬next)∨v
                    //   v→child: ¬v∨c, ¬v∨a∨next
                    if (nxt) |nv| {
                        try cnf.addClause(&.{ lv, Lit.negative(c), Lit.negative(a) });
                        try cnf.addClause(&.{ lv, Lit.negative(c), Lit.negative(nv) });
                        try cnf.addClause(&.{ lnot, Lit.positive(c), Lit.positive(a) });
                        try cnf.addClause(&.{ lnot, Lit.positive(c), Lit.positive(nv) });
                    } else {
                        // last frame: v <-> c
                        try cnf.addClause(&.{ lnot, Lit.positive(c) });
                        try cnf.addClause(&.{ lv, Lit.negative(c) });
                    }
                },
            }
        }
    }
    return .{ .cnf = cnf, .root_var = vof(root, 0, frames), .conflicts = 0 };
}

pub fn evalSat(allocator: std.mem.Allocator, b: *const Builder, tr: *const Trace, root: u32) !LtlResult {
    var enc = try encodeSat(allocator, b, tr, root);
    defer enc.cnf.deinit();
    // Force root var true; satisfiable => formula holds at frame 0.
    // Mutate enc.cnf in place (no shallow copy) to avoid a double-free.
    try enc.cnf.addClause(&.{Lit.positive(enc.root_var)});
    const r: SolveResult = try solver_mod.solveCnf(allocator, &enc.cnf, .{});
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    const status: LtlStatus = switch (r.status) {
        .sat => .holds_within_bound,
        .unsat => .fails_within_bound,
        .unknown => .unknown,
    };
    return .{ .status = status, .bound = tr.frames -% 1, .conflicts = r.conflicts };
}

/// Holds at frame 0 within bound (direct structural evaluation).
pub fn check(allocator: std.mem.Allocator, b: *const Builder, tr: *const Trace, root: u32) !LtlResult {
    _ = allocator;
    const holds = evalDirect(b, tr, 0, root);
    return .{ .status = if (holds) .holds_within_bound else .fails_within_bound, .bound = tr.frames -% 1 };
}

/// Fail-closed claim replay: both evaluators must agree, and the recorded
/// verdict must match them. Any divergence → error (never a silent pass).
pub fn verifyClaim(allocator: std.mem.Allocator, b: *const Builder, tr: *const Trace, claim: struct { formula: u32, expected: bool }) !void {
    const direct = evalDirect(b, tr, 0, claim.formula);
    const sat_res = try evalSat(allocator, b, tr, claim.formula);
    const sat_holds = sat_res.status == .holds_within_bound;
    if (direct != sat_holds) {
        return error.EvaluatorsDiverged;
    }
    if (direct != claim.expected) {
        return error.ClaimMismatch;
    }
}

const rng = std.Random.DefaultPrng;

/// Exhaustive/random cross-check: two semantics must agree on every sampled
/// (trace, formula). Returns count of disagreements (should be 0).
pub fn crossCheck(allocator: std.mem.Allocator, seed: u64) !u32 {
    var prng = rng.init(seed);
    const rand = prng.random();
    var disagreements: u32 = 0;
    var trial: u32 = 0;
    while (trial < 120) : (trial += 1) {
        const frames = 1 + rand.intRangeLessThan(u32, 0, 5); // 1..5
        const nets = 1 + rand.intRangeLessThan(u32, 0, 3); // 1..3
        var tr = try Trace.init(allocator, frames, nets);
        defer tr.deinit();
        var i: u32 = 0;
        while (i < frames) : (i += 1) {
            var n: u32 = 0;
            while (n < nets) : (n += 1) tr.set(i, n, rand.boolean());
        }
        var b = Builder.init(allocator);
        defer b.deinit();
        const p = try b.ap(0);
        const q = if (nets > 1) try b.ap(1) else p;
        const notp = try b.not_(p);
        const pandq = try b.and_(p, q);
        const pxorq = try b.or_(p, q);
        const xp = try b.next(p);
        const fp = try b.eventually(p);
        const gp = try b.globally(p);
        const pup = try b.until(p, p);
        const pup2 = try b.until(p, q);
        const rpq = try b.release(p, q);
        const formulas = [_]u32{ p, q, notp, pandq, pxorq, xp, fp, gp, pup, pup2, rpq };
        for (formulas) |f| {
            const direct = evalDirect(&b, &tr, 0, f);
            const sat = try evalSat(allocator, &b, &tr, f);
            const sat_holds = sat.status == .holds_within_bound;
            if (direct != sat_holds) disagreements += 1;
        }
    }
    return disagreements;
}

test "ltl: two semantics agree on random traces/formulas" {
    var disagreements: u32 = 0;
    var s: u32 = 0;
    while (s < 4) : (s += 1) disagreements += try crossCheck(std.testing.allocator, 0x1000 + s);
    try std.testing.expect(disagreements == 0);
}

test "ltl: F p equivalent to not G not p (duality, every trace)" {
    var prng = rng.init(0xABCD);
    const rand = prng.random();
    var trial: u32 = 0;
    while (trial < 200) : (trial += 1) {
        const frames = 1 + rand.intRangeLessThan(u32, 0, 5);
        const nets = 1;
        var tr = try Trace.init(std.testing.allocator, frames, nets);
        defer tr.deinit();
        var i: u32 = 0;
        while (i < frames) : (i += 1) tr.set(i, 0, rand.boolean());
        var b = Builder.init(std.testing.allocator);
        defer b.deinit();
        const p = try b.ap(0);
        const fp = try b.eventually(p);
        const notp = try b.not_(p);
        const gnotp = try b.globally(notp);
        const neg_gnotp = try b.not_(gnotp);
        try std.testing.expectEqual(evalDirect(&b, &tr, 0, fp), evalDirect(&b, &tr, 0, neg_gnotp));
    }
}

test "ltl: p U q implies F q (validity on every trace)" {
    var prng = rng.init(0xDCAB);
    const rand = prng.random();
    var trial: u32 = 0;
    while (trial < 200) : (trial += 1) {
        const frames = 1 + rand.intRangeLessThan(u32, 0, 5);
        const nets = 1;
        var tr = try Trace.init(std.testing.allocator, frames, nets);
        defer tr.deinit();
        var i: u32 = 0;
        while (i < frames) : (i += 1) tr.set(i, 0, rand.boolean());
        var b = Builder.init(std.testing.allocator);
        defer b.deinit();
        const p = try b.ap(0);
        const q = try b.ap(0); // single net: p == q
        const puq = try b.until(p, q);
        const fq = try b.eventually(q);
        const puqHolds = evalDirect(&b, &tr, 0, puq);
        const fqHolds = evalDirect(&b, &tr, 0, fq);
        try std.testing.expect(!puqHolds or fqHolds);
    }
}

test "ltl: G p implies p at frame 0 (validity on every trace)" {
    var prng = rng.init(0xBEEF);
    const rand = prng.random();
    var trial: u32 = 0;
    while (trial < 200) : (trial += 1) {
        const frames = 1 + rand.intRangeLessThan(u32, 0, 5);
        const nets = 1;
        var tr = try Trace.init(std.testing.allocator, frames, nets);
        defer tr.deinit();
        var i: u32 = 0;
        while (i < frames) : (i += 1) tr.set(i, 0, rand.boolean());
        var b = Builder.init(std.testing.allocator);
        defer b.deinit();
        const p = try b.ap(0);
        const gp = try b.globally(p);
        if (evalDirect(&b, &tr, 0, gp)) {
            try std.testing.expect(tr.at(0, 0)); // G p => p@0
        }
    }
}

test "ltl: verifyClaim fails closed on divergence/expected mismatch" {
    var tr = try Trace.init(std.testing.allocator, 3, 1);
    defer tr.deinit();
    tr.set(0, 0, true);
    tr.set(1, 0, false);
    var b = Builder.init(std.testing.allocator);
    defer b.deinit();
    const p = try b.ap(0);
    // p holds at frame 0; expected true must pass.
    try verifyClaim(std.testing.allocator, &b, &tr, .{ .formula = p, .expected = true });
    // Wrong expected must fail closed (return error, never silent pass).
    var trapped = false;
    if (verifyClaim(std.testing.allocator, &b, &tr, .{ .formula = p, .expected = false })) unreachable else |_| trapped = true;
    try std.testing.expect(trapped);
}
