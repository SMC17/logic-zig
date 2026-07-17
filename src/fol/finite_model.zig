//! Finite-model evaluation and small-domain search for FOL sentences.
//!
//! Supports unary/binary predicates and unary/binary total functions on
//! domain {0..d-1}, with an explicit search-space budget.

const std = @import("std");
const term_mod = @import("term.zig");
const TermPool = term_mod.TermPool;
const FormulaPool = term_mod.FormulaPool;
const FormulaId = term_mod.FormulaId;
const TermId = term_mod.TermId;

pub const Interpretation = struct {
    allocator: std.mem.Allocator,
    domain: u32,
    consts: std.StringHashMapUnmanaged(u32) = .{},
    preds: std.StringHashMapUnmanaged([]u8) = .{},
    funcs: std.StringHashMapUnmanaged([]u32) = .{},

    pub fn init(allocator: std.mem.Allocator, domain: u32) Interpretation {
        return .{ .allocator = allocator, .domain = domain };
    }

    pub fn deinit(self: *Interpretation) void {
        var pit = self.preds.iterator();
        while (pit.next()) |e| {
            self.allocator.free(e.key_ptr.*);
            self.allocator.free(e.value_ptr.*);
        }
        self.preds.deinit(self.allocator);
        var fit = self.funcs.iterator();
        while (fit.next()) |e| {
            self.allocator.free(e.key_ptr.*);
            self.allocator.free(e.value_ptr.*);
        }
        self.funcs.deinit(self.allocator);
        self.consts.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn setConst(self: *Interpretation, name: []const u8, val: u32) !void {
        try self.consts.put(self.allocator, name, val);
    }

    fn key(allocator: std.mem.Allocator, name: []const u8, arity: u16) ![]u8 {
        return std.fmt.allocPrint(allocator, "{s}/{d}", .{ name, arity });
    }

    pub fn ensurePred(self: *Interpretation, name: []const u8, arity: u16) !void {
        const k = try key(self.allocator, name, arity);
        defer self.allocator.free(k);
        if (self.preds.contains(k)) return;
        const size = std.math.pow(usize, self.domain, arity);
        const table = try self.allocator.alloc(u8, size);
        @memset(table, 0);
        const owned_key = try self.allocator.dupe(u8, k);
        try self.preds.put(self.allocator, owned_key, table);
    }

    pub fn setPred(self: *Interpretation, name: []const u8, args: []const u32, val: bool) !void {
        try self.ensurePred(name, @intCast(args.len));
        const k = try key(self.allocator, name, @intCast(args.len));
        defer self.allocator.free(k);
        const table = self.preds.get(k).?;
        table[flatIndex(self.domain, args)] = if (val) 1 else 0;
    }

    pub fn getPred(self: *const Interpretation, name: []const u8, args: []const u32) bool {
        const k = key(self.allocator, name, @intCast(args.len)) catch return false;
        defer self.allocator.free(k);
        const table = self.preds.get(k) orelse return false;
        return table[flatIndex(self.domain, args)] != 0;
    }

    pub fn ensureFunc(self: *Interpretation, name: []const u8, arity: u16) !void {
        const k = try key(self.allocator, name, arity);
        defer self.allocator.free(k);
        if (self.funcs.contains(k)) return;
        const size = std.math.pow(usize, self.domain, arity);
        const table = try self.allocator.alloc(u32, size);
        @memset(table, 0);
        const owned_key = try self.allocator.dupe(u8, k);
        try self.funcs.put(self.allocator, owned_key, table);
    }

    pub fn setFunc(self: *Interpretation, name: []const u8, args: []const u32, val: u32) !void {
        try self.ensureFunc(name, @intCast(args.len));
        const k = try key(self.allocator, name, @intCast(args.len));
        defer self.allocator.free(k);
        const table = self.funcs.get(k).?;
        table[flatIndex(self.domain, args)] = val;
    }

    pub fn getFunc(self: *const Interpretation, name: []const u8, args: []const u32) ?u32 {
        const k = key(self.allocator, name, @intCast(args.len)) catch return null;
        defer self.allocator.free(k);
        const table = self.funcs.get(k) orelse return null;
        return table[flatIndex(self.domain, args)];
    }
};

fn flatIndex(domain: u32, args: []const u32) usize {
    var idx: usize = 0;
    for (args) |a| {
        idx = idx * domain + a;
    }
    return idx;
}

const Env = std.StringHashMapUnmanaged(u32);

fn evalTerm(pool: *const TermPool, interp: *const Interpretation, env: *const Env, t: TermId) ?u32 {
    switch (pool.tag(t)) {
        .variable => return env.get(pool.nameOf(t)),
        .constant => return interp.consts.get(pool.nameOf(t)) orelse 0,
        .func => {
            const args = pool.argsOf(t);
            if (args.len == 0) return interp.consts.get(pool.nameOf(t)) orelse 0;
            var buf: [8]u32 = undefined;
            if (args.len > buf.len) return null;
            for (args, 0..) |a, i| {
                buf[i] = evalTerm(pool, interp, env, a) orelse return null;
            }
            return interp.getFunc(pool.nameOf(t), buf[0..args.len]);
        },
    }
}

pub fn evalFormula(
    fpool: *const FormulaPool,
    interp: *const Interpretation,
    env: *Env,
    f: FormulaId,
) !bool {
    const pool = fpool.terms;
    return switch (fpool.tagOf(f)) {
        .false_ => false,
        .true_ => true,
        .atom => blk: {
            const args_t = fpool.atomArgs(f);
            var buf: [8]u32 = undefined;
            if (args_t.len > buf.len) return error.TooManyArgs;
            for (args_t, 0..) |t, i| {
                buf[i] = evalTerm(pool, interp, env, t) orelse return error.Unbound;
            }
            break :blk interp.getPred(fpool.atomPred(f), buf[0..args_t.len]);
        },
        .eq => blk: {
            const l = evalTerm(pool, interp, env, fpool.eqLeft(f)) orelse return error.Unbound;
            const r = evalTerm(pool, interp, env, fpool.eqRight(f)) orelse return error.Unbound;
            break :blk l == r;
        },
        .not => !(try evalFormula(fpool, interp, env, fpool.left(f))),
        .and_ => (try evalFormula(fpool, interp, env, fpool.left(f))) and
            (try evalFormula(fpool, interp, env, fpool.right(f))),
        .or_ => (try evalFormula(fpool, interp, env, fpool.left(f))) or
            (try evalFormula(fpool, interp, env, fpool.right(f))),
        .implies => {
            const a = try evalFormula(fpool, interp, env, fpool.left(f));
            if (!a) return true;
            return try evalFormula(fpool, interp, env, fpool.right(f));
        },
        .forall => {
            const v = fpool.binderVar(f);
            const vname = pool.nameOf(v);
            const body = fpool.binderBody(f);
            var e: u32 = 0;
            while (e < interp.domain) : (e += 1) {
                try env.put(fpool.allocator, vname, e);
                if (!try evalFormula(fpool, interp, env, body)) return false;
            }
            return true;
        },
        .exists => {
            const v = fpool.binderVar(f);
            const vname = pool.nameOf(v);
            const body = fpool.binderBody(f);
            var e: u32 = 0;
            while (e < interp.domain) : (e += 1) {
                try env.put(fpool.allocator, vname, e);
                if (try evalFormula(fpool, interp, env, body)) return true;
            }
            return false;
        },
    };
}

pub const ModelResult = struct {
    sat: bool,
    model: ?Interpretation = null,
    explored: u64 = 0,
};

pub const PredSpec = struct {
    name: []const u8,
    arity: u16,
};

pub const FuncSpec = struct {
    name: []const u8,
    arity: u16,
};

pub const Signature = struct {
    preds: []const PredSpec = &.{},
    funcs: []const FuncSpec = &.{},
    /// Hard cap on enumerated interpretations (default 200_000).
    max_models: u64 = 200_000,
};

fn predSlots(domain: u32, arity: u16) u32 {
    return @intCast(std.math.pow(usize, domain, arity));
}

fn funcSlots(domain: u32, arity: u16) u32 {
    // table size = domain^arity cells, each cell ∈ [0, domain)
    return @intCast(std.math.pow(usize, domain, arity));
}

/// Search for a finite model over the given signature.
pub fn findModel(
    allocator: std.mem.Allocator,
    fpool: *FormulaPool,
    sentence: FormulaId,
    domain: u32,
    sig: Signature,
) !ModelResult {
    if (domain == 0 or domain > 4) return error.DomainTooLarge;
    for (sig.preds) |p| {
        if (p.arity == 0 or p.arity > 2) return error.UnsupportedArity;
    }
    for (sig.funcs) |f| {
        if (f.arity == 0 or f.arity > 2) return error.UnsupportedArity;
    }

    // Digits for mixed-radix enumeration.
    // Pred tables: each cell is 0/1 → radix 2, count = domain^arity bits.
    // Func tables: each cell is 0..d-1 → radix d, count = domain^arity cells.
    var digit_radices: std.ArrayList(u32) = .empty;
    defer digit_radices.deinit(allocator);
    var digit_meta: std.ArrayList(struct { kind: enum { pred, func }, name: []const u8, arity: u16, cell: u32 }) = .empty;
    defer digit_meta.deinit(allocator);

    for (sig.preds) |p| {
        const cells = predSlots(domain, p.arity);
        var c: u32 = 0;
        while (c < cells) : (c += 1) {
            try digit_radices.append(allocator, 2);
            try digit_meta.append(allocator, .{ .kind = .pred, .name = p.name, .arity = p.arity, .cell = c });
        }
    }
    for (sig.funcs) |f| {
        const cells = funcSlots(domain, f.arity);
        var c: u32 = 0;
        while (c < cells) : (c += 1) {
            try digit_radices.append(allocator, domain);
            try digit_meta.append(allocator, .{ .kind = .func, .name = f.name, .arity = f.arity, .cell = c });
        }
    }

    if (digit_radices.items.len == 0) {
        // No signature — evaluate once under empty interp.
        var interp = Interpretation.init(allocator, domain);
        var env: Env = .{};
        defer env.deinit(allocator);
        const ok = try evalFormula(fpool, &interp, &env, sentence);
        if (ok) return .{ .sat = true, .model = interp, .explored = 1 };
        interp.deinit();
        return .{ .sat = false, .explored = 1 };
    }

    // Enumerate odometer-style.
    const digits = try allocator.alloc(u32, digit_radices.items.len);
    defer allocator.free(digits);
    @memset(digits, 0);

    var explored: u64 = 0;
    while (true) {
        explored += 1;
        if (explored > sig.max_models) return error.SearchBudget;

        var interp = Interpretation.init(allocator, domain);
        errdefer interp.deinit();

        // Materialize.
        for (digits, 0..) |dval, di| {
            const m = digit_meta.items[di];
            // Decode cell index into args.
            var args_buf: [2]u32 = .{ 0, 0 };
            var tmp = m.cell;
            var a: i32 = @intCast(m.arity);
            while (a > 0) {
                a -= 1;
                args_buf[@intCast(a)] = tmp % domain;
                tmp /= domain;
            }
            const args = args_buf[0..m.arity];
            switch (m.kind) {
                .pred => try interp.setPred(m.name, args, dval != 0),
                .func => try interp.setFunc(m.name, args, dval),
            }
        }

        var env: Env = .{};
        defer env.deinit(allocator);
        const ok = evalFormula(fpool, &interp, &env, sentence) catch {
            interp.deinit();
            if (!odometerInc(digits, digit_radices.items)) break;
            continue;
        };
        if (ok) {
            return .{ .sat = true, .model = interp, .explored = explored };
        }
        interp.deinit();

        if (!odometerInc(digits, digit_radices.items)) break;
    }
    return .{ .sat = false, .explored = explored };
}

fn odometerInc(digits: []u32, radices: []const u32) bool {
    var i: isize = @intCast(digits.len);
    i -= 1;
    while (i >= 0) : (i -= 1) {
        const ui: usize = @intCast(i);
        digits[ui] += 1;
        if (digits[ui] < radices[ui]) return true;
        digits[ui] = 0;
    }
    return false;
}

/// Convenience: unary predicates only.
pub fn findUnaryModel(
    allocator: std.mem.Allocator,
    fpool: *FormulaPool,
    sentence: FormulaId,
    domain: u32,
    pred_names: []const []const u8,
) !ModelResult {
    var specs: std.ArrayList(PredSpec) = .empty;
    defer specs.deinit(allocator);
    for (pred_names) |n| try specs.append(allocator, .{ .name = n, .arity = 1 });
    return findModel(allocator, fpool, sentence, domain, .{ .preds = specs.items });
}

test "forall exists on tiny domain" {
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();

    const x = try terms.mkVar("x");
    const px = try fpool.mkAtom("P", &.{x});
    const sentence = try fpool.mkExists(x, px);

    const r = try findUnaryModel(std.testing.allocator, &fpool, sentence, 2, &.{"P"});
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);

    const x2 = try terms.mkVar("x");
    const all = try fpool.mkForall(x2, try fpool.mkAtom("P", &.{x2}));
    const x3 = try terms.mkVar("x");
    const some_not = try fpool.mkExists(x3, try fpool.mkNot(try fpool.mkAtom("P", &.{x3})));
    const bad = try fpool.mkAnd(all, some_not);
    const r2 = try findUnaryModel(std.testing.allocator, &fpool, bad, 2, &.{"P"});
    defer if (r2.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(!r2.sat);
}

test "binary relation asymmetric model" {
    // ∃x∃y R(x,y) ∧ ¬R(y,x) on domain 2
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();

    const x = try terms.mkVar("x");
    const y = try terms.mkVar("y");
    const rxy = try fpool.mkAtom("R", &.{ x, y });
    const ryx = try fpool.mkAtom("R", &.{ y, x });
    const body = try fpool.mkAnd(rxy, try fpool.mkNot(ryx));
    const sentence = try fpool.mkExists(x, try fpool.mkExists(y, body));

    const r = try findModel(std.testing.allocator, &fpool, sentence, 2, .{
        .preds = &.{.{ .name = "R", .arity = 2 }},
    });
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);
}

test "unary function involution model" {
    // ∃x f(f(x)) = x  — always true for total f on finite domain if we only
    // ask existence of a fixed point of f∘f, which is always true.
    // Stronger: ∀x f(f(x))=x (involution) — has models (identity, swap on d=2).
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();

    const x = try terms.mkVar("x");
    const fx = try terms.mkFunc("f", &.{x});
    const ffx = try terms.mkFunc("f", &.{fx});
    const eq = try fpool.mkEq(ffx, x);
    const sentence = try fpool.mkForall(x, eq);

    const r = try findModel(std.testing.allocator, &fpool, sentence, 2, .{
        .funcs = &.{.{ .name = "f", .arity = 1 }},
    });
    defer if (r.model) |*m| {
        var mm = m.*;
        mm.deinit();
    };
    try std.testing.expect(r.sat);
}
