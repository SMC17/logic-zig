//! Encode finite-model search as SAT (scales past brute odometer for larger tables).
//!
//! For domain size d:
//! - Pred P/arity: one Boolean var per tuple
//! - Func f/arity: d Boolean vars per tuple (one-hot code of result), exactly-one
//! Quantifiers expand over the domain. Equality is syntactic on domain ids.

const std = @import("std");
const term_mod = @import("term.zig");
const fm = @import("finite_model.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const TermPool = term_mod.TermPool;
const FormulaPool = term_mod.FormulaPool;
const FormulaId = term_mod.FormulaId;
const TermId = term_mod.TermId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Signature = fm.Signature;
const PredSpec = fm.PredSpec;
const FuncSpec = fm.FuncSpec;
const ModelResult = fm.ModelResult;
const Interpretation = fm.Interpretation;

const Env = std.StringHashMapUnmanaged(u32);

const Encoder = struct {
    allocator: std.mem.Allocator,
    domain: u32,
    cnf: Cnf,
    /// next free var index
    next_var: u32 = 0,
    /// "P/2:i,j" → var
    pred_vars: std.StringHashMapUnmanaged(u32) = .{},
    /// "f/1:i:r" → var (one-hot)
    func_vars: std.StringHashMapUnmanaged(u32) = .{},
    sig: Signature,

    fn deinit(self: *Encoder) void {
        var it = self.pred_vars.iterator();
        while (it.next()) |e| self.allocator.free(e.key_ptr.*);
        self.pred_vars.deinit(self.allocator);
        var ft = self.func_vars.iterator();
        while (ft.next()) |e| self.allocator.free(e.key_ptr.*);
        self.func_vars.deinit(self.allocator);
        self.cnf.deinit();
    }

    fn fresh(self: *Encoder) u32 {
        const v = self.next_var;
        self.next_var += 1;
        self.cnf.ensureVars(self.next_var);
        return v;
    }

    fn predKey(self: *Encoder, name: []const u8, args: []const u32) ![]u8 {
        var aw: std.Io.Writer.Allocating = .init(self.allocator);
        defer aw.deinit();
        try aw.writer.print("{s}/{d}:", .{ name, args.len });
        for (args, 0..) |a, i| {
            if (i > 0) try aw.writer.writeAll(",");
            try aw.writer.print("{d}", .{a});
        }
        return try aw.toOwnedSlice();
    }

    fn funcKey(self: *Encoder, name: []const u8, args: []const u32, result: u32) ![]u8 {
        var aw: std.Io.Writer.Allocating = .init(self.allocator);
        defer aw.deinit();
        try aw.writer.print("{s}/{d}:", .{ name, args.len });
        for (args, 0..) |a, i| {
            if (i > 0) try aw.writer.writeAll(",");
            try aw.writer.print("{d}", .{a});
        }
        try aw.writer.print(":{d}", .{result});
        return try aw.toOwnedSlice();
    }

    fn predLit(self: *Encoder, name: []const u8, args: []const u32, neg: bool) !Lit {
        const k = try self.predKey(name, args);
        defer self.allocator.free(k);
        if (self.pred_vars.get(k)) |vi| {
            return Lit.make(Var.fromIndex(vi), neg);
        }
        const vi = self.fresh();
        const owned = try self.allocator.dupe(u8, k);
        try self.pred_vars.put(self.allocator, owned, vi);
        return Lit.make(Var.fromIndex(vi), neg);
    }

    fn funcLit(self: *Encoder, name: []const u8, args: []const u32, result: u32, neg: bool) !Lit {
        const k = try self.funcKey(name, args, result);
        defer self.allocator.free(k);
        if (self.func_vars.get(k)) |vi| {
            return Lit.make(Var.fromIndex(vi), neg);
        }
        const vi = self.fresh();
        const owned = try self.allocator.dupe(u8, k);
        try self.func_vars.put(self.allocator, owned, vi);
        return Lit.make(Var.fromIndex(vi), neg);
    }

    fn encodeFuncExactlyOne(self: *Encoder) !void {
        for (self.sig.funcs) |f| {
            const cells = std.math.pow(usize, self.domain, f.arity);
            var cell: u32 = 0;
            while (cell < cells) : (cell += 1) {
                var args: [2]u32 = .{ 0, 0 };
                var tmp = cell;
                var a: i32 = @intCast(f.arity);
                while (a > 0) {
                    a -= 1;
                    args[@intCast(a)] = tmp % self.domain;
                    tmp /= self.domain;
                }
                const arg_slice = args[0..f.arity];
                // at least one
                var least: std.ArrayList(Lit) = .empty;
                defer least.deinit(self.allocator);
                var r: u32 = 0;
                while (r < self.domain) : (r += 1) {
                    try least.append(self.allocator, try self.funcLit(f.name, arg_slice, r, false));
                }
                try self.cnf.addClause(least.items);
                // at most one
                r = 0;
                while (r < self.domain) : (r += 1) {
                    var s = r + 1;
                    while (s < self.domain) : (s += 1) {
                        const l1 = try self.funcLit(f.name, arg_slice, r, true);
                        const l2 = try self.funcLit(f.name, arg_slice, s, true);
                        try self.cnf.addClause(&.{ l1, l2 });
                    }
                }
            }
        }
    }

    fn evalTermToCases(
        self: *Encoder,
        pool: *const TermPool,
        env: *const Env,
        t: TermId,
        out_vals: *std.ArrayList(u32),
        out_guards: *std.ArrayList(?Lit),
    ) !void {
        // Produce list of (value, guard_lit?) meaning under guard term equals value.
        // guard null = always.
        out_vals.clearRetainingCapacity();
        out_guards.clearRetainingCapacity();
        switch (pool.tag(t)) {
            .variable => {
                const v = env.get(pool.nameOf(t)) orelse return error.Unbound;
                try out_vals.append(self.allocator, v);
                try out_guards.append(self.allocator, null);
            },
            .constant => {
                const v = env.get(pool.nameOf(t)) orelse @as(u32, 0); // const map via name digits?
                // Constants: use env only if bound; else try parse as domain int or default 0.
                // Better: constants fixed by name lookup in a const map — use 0 default.
                _ = v;
                const name = pool.nameOf(t);
                // Map first d constant names a,b,c... or use 0
                var code: u32 = 0;
                if (name.len > 0) code = name[0] % self.domain;
                try out_vals.append(self.allocator, code);
                try out_guards.append(self.allocator, null);
            },
            .func => {
                const args = pool.argsOf(t);
                if (args.len == 0) {
                    try out_vals.append(self.allocator, 0);
                    try out_guards.append(self.allocator, null);
                    return;
                }
                if (args.len > 2) return error.UnsupportedArity;
                // Expand Cartesian product of argument cases, then range of f.
                // arg_cases[j] = list of (val, guard) for args[j]
                var a0v: std.ArrayList(u32) = .empty;
                defer a0v.deinit(self.allocator);
                var a0g: std.ArrayList(?Lit) = .empty;
                defer a0g.deinit(self.allocator);
                try self.evalTermToCases(pool, env, args[0], &a0v, &a0g);

                if (args.len == 1) {
                    var i: usize = 0;
                    while (i < a0v.items.len) : (i += 1) {
                        try self.appendFuncResults(pool.nameOf(t), &.{a0v.items[i]}, a0g.items[i], out_vals, out_guards);
                    }
                    return;
                }
                // binary
                var a1v: std.ArrayList(u32) = .empty;
                defer a1v.deinit(self.allocator);
                var a1g: std.ArrayList(?Lit) = .empty;
                defer a1g.deinit(self.allocator);
                try self.evalTermToCases(pool, env, args[1], &a1v, &a1g);
                var i: usize = 0;
                while (i < a0v.items.len) : (i += 1) {
                    var j: usize = 0;
                    while (j < a1v.items.len) : (j += 1) {
                        const g = try self.conjGuards(a0g.items[i], a1g.items[j]);
                        try self.appendFuncResults(pool.nameOf(t), &.{ a0v.items[i], a1v.items[j] }, g, out_vals, out_guards);
                    }
                }
            },
        }
    }

    fn conjGuards(self: *Encoder, a: ?Lit, b: ?Lit) !?Lit {
        if (a == null and b == null) return null;
        if (a == null) return b;
        if (b == null) return a;
        const conj = self.fresh();
        const cl = Lit.positive(Var.fromIndex(conj));
        try self.cnf.addClause(&.{ cl.not(), a.? });
        try self.cnf.addClause(&.{ cl.not(), b.? });
        try self.cnf.addClause(&.{ a.?.not(), b.?.not(), cl });
        return cl;
    }

    fn appendFuncResults(
        self: *Encoder,
        name: []const u8,
        arg_vals: []const u32,
        arg_g: ?Lit,
        out_vals: *std.ArrayList(u32),
        out_guards: *std.ArrayList(?Lit),
    ) !void {
        var r: u32 = 0;
        while (r < self.domain) : (r += 1) {
            const fl = try self.funcLit(name, arg_vals, r, false);
            const conj = self.fresh();
            const cl = Lit.positive(Var.fromIndex(conj));
            try self.cnf.addClause(&.{ cl.not(), fl });
            if (arg_g) |g| {
                try self.cnf.addClause(&.{ cl.not(), g });
                try self.cnf.addClause(&.{ g.not(), fl.not(), cl });
            } else {
                try self.cnf.addClause(&.{ fl.not(), cl });
            }
            try out_vals.append(self.allocator, r);
            try out_guards.append(self.allocator, cl);
        }
    }

    fn encodeFormula(self: *Encoder, fpool: *const FormulaPool, env: *Env, f: FormulaId) !Lit {
        // Returns a literal equivalent to formula under env (Tseitin-ish).
        const pool = fpool.terms;
        switch (fpool.tagOf(f)) {
            .false_ => {
                const v = self.fresh();
                try self.cnf.addClause(&.{Lit.negative(Var.fromIndex(v))});
                return Lit.positive(Var.fromIndex(v));
            },
            .true_ => {
                const v = self.fresh();
                try self.cnf.addClause(&.{Lit.positive(Var.fromIndex(v))});
                return Lit.positive(Var.fromIndex(v));
            },
            .atom => {
                const args_t = fpool.atomArgs(f);
                var args: [2]u32 = undefined;
                if (args_t.len > 2) return error.TooManyArgs;
                for (args_t, 0..) |t, i| {
                    var av: std.ArrayList(u32) = .empty;
                    defer av.deinit(self.allocator);
                    var ag: std.ArrayList(?Lit) = .empty;
                    defer ag.deinit(self.allocator);
                    try self.evalTermToCases(pool, env, t, &av, &ag);
                    if (av.items.len != 1) {
                        // functional — expand (rare in tests); take first only if guarded
                        return error.NonGround;
                    }
                    args[i] = av.items[0];
                }
                return try self.predLit(fpool.atomPred(f), args[0..args_t.len], false);
            },
            .eq => {
                var lv: std.ArrayList(u32) = .empty;
                defer lv.deinit(self.allocator);
                var lg: std.ArrayList(?Lit) = .empty;
                defer lg.deinit(self.allocator);
                var rv: std.ArrayList(u32) = .empty;
                defer rv.deinit(self.allocator);
                var rg: std.ArrayList(?Lit) = .empty;
                defer rg.deinit(self.allocator);
                try self.evalTermToCases(pool, env, fpool.eqLeft(f), &lv, &lg);
                try self.evalTermToCases(pool, env, fpool.eqRight(f), &rv, &rg);
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                // out ↔ ∨_{i,j: lv_i=rv_j} (gi ∧ gj)
                // Encode: for each equal pair, gi∧gj → out; and out → big or
                var or_lits: std.ArrayList(Lit) = .empty;
                defer or_lits.deinit(self.allocator);
                for (lv.items, 0..) |lvv, i| {
                    for (rv.items, 0..) |rvv, j| {
                        if (lvv != rvv) continue;
                        const conj = self.fresh();
                        const cl = Lit.positive(Var.fromIndex(conj));
                        // conj → guards
                        if (lg.items[i]) |g| try self.cnf.addClause(&.{ cl.not(), g });
                        if (rg.items[j]) |g| try self.cnf.addClause(&.{ cl.not(), g });
                        // guards → conj (if both null, conj true)
                        if (lg.items[i] == null and rg.items[j] == null) {
                            try self.cnf.addClause(&.{cl});
                        } else if (lg.items[i] == null) {
                            try self.cnf.addClause(&.{ rg.items[j].?.not(), cl });
                        } else if (rg.items[j] == null) {
                            try self.cnf.addClause(&.{ lg.items[i].?.not(), cl });
                        } else {
                            try self.cnf.addClause(&.{ lg.items[i].?.not(), rg.items[j].?.not(), cl });
                        }
                        try self.cnf.addClause(&.{ cl.not(), ol });
                        try or_lits.append(self.allocator, cl);
                    }
                }
                if (or_lits.items.len == 0) {
                    try self.cnf.addClause(&.{ol.not()});
                } else {
                    var clause: std.ArrayList(Lit) = .empty;
                    defer clause.deinit(self.allocator);
                    try clause.append(self.allocator, ol.not());
                    for (or_lits.items) |x| try clause.append(self.allocator, x);
                    try self.cnf.addClause(clause.items);
                }
                return ol;
            },
            .not => {
                const inner = try self.encodeFormula(fpool, env, fpool.left(f));
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                // out ↔ ~inner
                try self.cnf.addClause(&.{ ol.not(), inner.not() });
                try self.cnf.addClause(&.{ inner, ol });
                return ol;
            },
            .and_ => {
                const a = try self.encodeFormula(fpool, env, fpool.left(f));
                const b = try self.encodeFormula(fpool, env, fpool.right(f));
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                try self.cnf.addClause(&.{ ol.not(), a });
                try self.cnf.addClause(&.{ ol.not(), b });
                try self.cnf.addClause(&.{ a.not(), b.not(), ol });
                return ol;
            },
            .or_ => {
                const a = try self.encodeFormula(fpool, env, fpool.left(f));
                const b = try self.encodeFormula(fpool, env, fpool.right(f));
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                try self.cnf.addClause(&.{ ol.not(), a, b });
                try self.cnf.addClause(&.{ a.not(), ol });
                try self.cnf.addClause(&.{ b.not(), ol });
                return ol;
            },
            .implies => {
                const a = try self.encodeFormula(fpool, env, fpool.left(f));
                const b = try self.encodeFormula(fpool, env, fpool.right(f));
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                // out ↔ ~a ∨ b
                try self.cnf.addClause(&.{ ol.not(), a.not(), b });
                try self.cnf.addClause(&.{ a, ol });
                try self.cnf.addClause(&.{ b.not(), ol });
                return ol;
            },
            .forall => {
                const vname = pool.nameOf(fpool.binderVar(f));
                const body = fpool.binderBody(f);
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(self.allocator);
                var e: u32 = 0;
                while (e < self.domain) : (e += 1) {
                    try env.put(self.allocator, vname, e);
                    try lits.append(self.allocator, try self.encodeFormula(fpool, env, body));
                }
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                for (lits.items) |x| try self.cnf.addClause(&.{ ol.not(), x });
                var clause: std.ArrayList(Lit) = .empty;
                defer clause.deinit(self.allocator);
                for (lits.items) |x| try clause.append(self.allocator, x.not());
                try clause.append(self.allocator, ol);
                try self.cnf.addClause(clause.items);
                return ol;
            },
            .exists => {
                const vname = pool.nameOf(fpool.binderVar(f));
                const body = fpool.binderBody(f);
                var lits: std.ArrayList(Lit) = .empty;
                defer lits.deinit(self.allocator);
                var e: u32 = 0;
                while (e < self.domain) : (e += 1) {
                    try env.put(self.allocator, vname, e);
                    try lits.append(self.allocator, try self.encodeFormula(fpool, env, body));
                }
                const out = self.fresh();
                const ol = Lit.positive(Var.fromIndex(out));
                // ol → ∨ body_e
                {
                    var c: std.ArrayList(Lit) = .empty;
                    defer c.deinit(self.allocator);
                    try c.append(self.allocator, ol.not());
                    for (lits.items) |x| try c.append(self.allocator, x);
                    try self.cnf.addClause(c.items);
                }
                // body_e → ol
                for (lits.items) |x| try self.cnf.addClause(&.{ x.not(), ol });
                return ol;
            },
        }
    }
};

/// SAT-based finite model finder. On success builds Interpretation from model.
pub fn findModelSat(
    allocator: std.mem.Allocator,
    fpool: *FormulaPool,
    sentence: FormulaId,
    domain: u32,
    sig: Signature,
) !ModelResult {
    if (domain == 0 or domain > 6) return error.DomainTooLarge;

    var enc = Encoder{
        .allocator = allocator,
        .domain = domain,
        .cnf = Cnf.init(allocator),
        .sig = sig,
    };
    defer enc.deinit();

    // Pre-create pred vars for all tuples so interpretation recovery works.
    for (sig.preds) |p| {
        const cells = std.math.pow(usize, domain, p.arity);
        var cell: u32 = 0;
        while (cell < cells) : (cell += 1) {
            var args: [2]u32 = .{ 0, 0 };
            var tmp = cell;
            var a: i32 = @intCast(p.arity);
            while (a > 0) {
                a -= 1;
                args[@intCast(a)] = tmp % domain;
                tmp /= domain;
            }
            _ = try enc.predLit(p.name, args[0..p.arity], false);
        }
    }
    try enc.encodeFuncExactlyOne();

    var env: Env = .{};
    defer env.deinit(allocator);
    const root = try enc.encodeFormula(fpool, &env, sentence);
    try enc.cnf.addClause(&.{root});

    const r = try solver_mod.solveCnf(allocator, &enc.cnf, .{});
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    if (r.status != .sat) {
        if (r.model) |m| allocator.free(m);
        return .{ .sat = false, .explored = 1 };
    }
    const model = r.model.?;
    defer allocator.free(model);

    var interp = Interpretation.init(allocator, domain);
    errdefer interp.deinit();

    for (sig.preds) |p| {
        try interp.ensurePred(p.name, p.arity);
        const cells = std.math.pow(usize, domain, p.arity);
        var cell: u32 = 0;
        while (cell < cells) : (cell += 1) {
            var args: [2]u32 = .{ 0, 0 };
            var tmp = cell;
            var a: i32 = @intCast(p.arity);
            while (a > 0) {
                a -= 1;
                args[@intCast(a)] = tmp % domain;
                tmp /= domain;
            }
            const lit = try enc.predLit(p.name, args[0..p.arity], false);
            const vi = lit.variable().index();
            const val = model[vi] == .true_;
            try interp.setPred(p.name, args[0..p.arity], val);
        }
    }
    for (sig.funcs) |f| {
        try interp.ensureFunc(f.name, f.arity);
        const cells = std.math.pow(usize, domain, f.arity);
        var cell: u32 = 0;
        while (cell < cells) : (cell += 1) {
            var args: [2]u32 = .{ 0, 0 };
            var tmp = cell;
            var a: i32 = @intCast(f.arity);
            while (a > 0) {
                a -= 1;
                args[@intCast(a)] = tmp % domain;
                tmp /= domain;
            }
            var rres: u32 = 0;
            while (rres < domain) : (rres += 1) {
                const lit = try enc.funcLit(f.name, args[0..f.arity], rres, false);
                if (model[lit.variable().index()] == .true_) {
                    try interp.setFunc(f.name, args[0..f.arity], rres);
                    break;
                }
            }
        }
    }

    return .{ .sat = true, .model = interp, .explored = 1 };
}

test "sat model binary R" {
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();
    const x = try terms.mkVar("x");
    const y = try terms.mkVar("y");
    const body = try fpool.mkAnd(
        try fpool.mkAtom("R", &.{ x, y }),
        try fpool.mkNot(try fpool.mkAtom("R", &.{ y, x })),
    );
    const sentence = try fpool.mkExists(x, try fpool.mkExists(y, body));
    const r = try findModelSat(std.testing.allocator, &fpool, sentence, 2, .{
        .preds = &.{.{ .name = "R", .arity = 2 }},
    });
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);
}

test "sat model involution" {
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();
    const x = try terms.mkVar("x");
    const fx = try terms.mkFunc("f", &.{x});
    const ffx = try terms.mkFunc("f", &.{fx});
    const sentence = try fpool.mkForall(x, try fpool.mkEq(ffx, x));
    const r = try findModelSat(std.testing.allocator, &fpool, sentence, 2, .{
        .funcs = &.{.{ .name = "f", .arity = 1 }},
    });
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);
}

test "sat model binary function projection" {
    // ∃x∃y f(x,y)=x  with binary f — should find left-projection models.
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();
    const x = try terms.mkVar("x");
    const y = try terms.mkVar("y");
    const fxy = try terms.mkFunc("f", &.{ x, y });
    const eq = try fpool.mkEq(fxy, x);
    const sentence = try fpool.mkExists(x, try fpool.mkExists(y, eq));
    const r = try findModelSat(std.testing.allocator, &fpool, sentence, 2, .{
        .funcs = &.{.{ .name = "f", .arity = 2 }},
    });
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);
}
