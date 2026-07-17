//! First-order terms and formulas with **semantically correct free-variable identity**.
//!
//! Free variables are unique `TermId`s (print names are metadata only). Quantifiers
//! bind a specific free-var `TermId`; nested binders that print as the same name
//! use different TermIds so shadowing is correct.
//!
//! Env evaluation keys by TermId index, never by printed name.

const std = @import("std");
const interner_mod = @import("../core/interner.zig");

pub const SymbolId = interner_mod.SymbolId;
pub const Interner = interner_mod.Interner;

pub const TermId = enum(u32) {
    _,
    pub fn index(self: TermId) u32 {
        return @intFromEnum(self);
    }
    pub fn fromIndex(i: u32) TermId {
        return @enumFromInt(i);
    }
};

pub const TermTag = enum(u8) {
    variable, // free or (when under quantifier) the free var used as binder key
    constant,
    func,
};

pub const FormulaId = enum(u32) {
    false_ = 0,
    true_ = 1,
    _,
    pub fn index(self: FormulaId) u32 {
        return @intFromEnum(self);
    }
    pub fn fromIndex(i: u32) FormulaId {
        return @enumFromInt(i);
    }
};

pub const FormulaTag = enum(u8) {
    false_,
    true_,
    atom,
    not,
    and_,
    or_,
    implies,
    forall,
    exists,
    eq,
};

pub const TermPool = struct {
    allocator: std.mem.Allocator,
    tags: std.ArrayList(TermTag) = .empty,
    /// For var/const: symbol; for func: function symbol.
    sym: std.ArrayList(u32) = .empty,
    arg_start: std.ArrayList(u32) = .empty,
    arity: std.ArrayList(u16) = .empty,
    arg_data: std.ArrayList(TermId) = .empty,
    interner: Interner,
    /// Constants still interned by name (rigid designators in syntax).
    const_by_name: std.StringHashMapUnmanaged(TermId) = .{},
    /// Monotonic free-var generation counter (for unique vars with same print name).
    free_gen: u32 = 0,

    pub fn init(allocator: std.mem.Allocator) TermPool {
        return .{
            .allocator = allocator,
            .interner = Interner.init(allocator),
        };
    }

    pub fn deinit(self: *TermPool) void {
        self.tags.deinit(self.allocator);
        self.sym.deinit(self.allocator);
        self.arg_start.deinit(self.allocator);
        self.arity.deinit(self.allocator);
        self.arg_data.deinit(self.allocator);
        self.const_by_name.deinit(self.allocator);
        self.interner.deinit();
        self.* = undefined;
    }

    /// Always allocate a **fresh** free variable. Print `name` is metadata only.
    /// Nested quantifiers must call this separately so binders do not collide.
    pub fn mkVar(self: *TermPool, name: []const u8) !TermId {
        self.free_gen += 1;
        // Intern "name#gen" for unique symbol storage while printName strips #gen for display.
        var buf: [128]u8 = undefined;
        const key = try std.fmt.bufPrint(&buf, "{s}\x1f{d}", .{ name, self.free_gen });
        const sid = try self.interner.intern(key);
        const id = TermId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, .variable);
        try self.sym.append(self.allocator, sid.index());
        try self.arg_start.append(self.allocator, 0);
        try self.arity.append(self.allocator, 0);
        return id;
    }

    /// Print name of a term (for vars, strip internal uniqueness suffix).
    pub fn printName(self: *const TermPool, t: TermId) []const u8 {
        const raw = self.interner.get(SymbolId.fromIndex(self.sym.items[t.index()]));
        if (self.tag(t) == .variable) {
            if (std.mem.indexOfScalar(u8, raw, 0x1f)) |sep| return raw[0..sep];
        }
        return raw;
    }

    pub fn mkConst(self: *TermPool, name: []const u8) !TermId {
        if (self.const_by_name.get(name)) |id| return id;
        const sid = try self.interner.intern(name);
        const id = TermId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, .constant);
        try self.sym.append(self.allocator, sid.index());
        try self.arg_start.append(self.allocator, 0);
        try self.arity.append(self.allocator, 0);
        const key = self.interner.get(sid);
        try self.const_by_name.put(self.allocator, key, id);
        return id;
    }

    pub fn mkFunc(self: *TermPool, name: []const u8, args: []const TermId) !TermId {
        const sid = try self.interner.intern(name);
        const start: u32 = @intCast(self.arg_data.items.len);
        try self.arg_data.appendSlice(self.allocator, args);
        const id = TermId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, .func);
        try self.sym.append(self.allocator, sid.index());
        try self.arg_start.append(self.allocator, start);
        try self.arity.append(self.allocator, @intCast(args.len));
        return id;
    }

    pub fn tag(self: *const TermPool, t: TermId) TermTag {
        return self.tags.items[t.index()];
    }

    /// Full interned key (includes uniqueness for vars). Prefer `printName` for UI.
    pub fn nameOf(self: *const TermPool, t: TermId) []const u8 {
        return self.printName(t);
    }

    pub fn rawNameOf(self: *const TermPool, t: TermId) []const u8 {
        return self.interner.get(SymbolId.fromIndex(self.sym.items[t.index()]));
    }

    pub fn argsOf(self: *const TermPool, t: TermId) []const TermId {
        const ar = self.arity.items[t.index()];
        const st = self.arg_start.items[t.index()];
        return self.arg_data.items[st .. st + ar];
    }

    pub fn isVar(self: *const TermPool, t: TermId) bool {
        return self.tag(t) == .variable;
    }

    pub fn isConst(self: *const TermPool, t: TermId) bool {
        return self.tag(t) == .constant;
    }
};

/// Environment: free-var TermId → domain element. Supports push/pop restore.
pub const Env = struct {
    map: std.AutoHashMapUnmanaged(u32, u32) = .{},
    stack: std.ArrayList(struct { key: u32, prev: ?u32, had: bool }) = .empty,
    allocator: std.mem.Allocator,

    pub fn init(allocator: std.mem.Allocator) Env {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Env) void {
        self.map.deinit(self.allocator);
        self.stack.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn get(self: *const Env, v: TermId) ?u32 {
        return self.map.get(v.index());
    }

    /// Bind `v` to `val`, saving previous binding for `pop`.
    pub fn push(self: *Env, v: TermId, val: u32) !void {
        const k = v.index();
        const had = self.map.contains(k);
        const prev = self.map.get(k);
        try self.stack.append(self.allocator, .{ .key = k, .prev = prev, .had = had });
        try self.map.put(self.allocator, k, val);
    }

    pub fn pop(self: *Env) void {
        const frame = self.stack.pop() orelse return;
        if (frame.had) {
            self.map.put(self.allocator, frame.key, frame.prev.?) catch {};
        } else {
            _ = self.map.remove(frame.key);
        }
    }
};

pub const FormulaPool = struct {
    allocator: std.mem.Allocator,
    terms: *TermPool,
    tags: std.ArrayList(FormulaTag) = .empty,
    a: std.ArrayList(u32) = .empty,
    b: std.ArrayList(u32) = .empty,
    pred: std.ArrayList(u32) = .empty,
    atom_arg_start: std.ArrayList(u32) = .empty,
    atom_arity: std.ArrayList(u16) = .empty,
    atom_args: std.ArrayList(TermId) = .empty,

    pub fn init(allocator: std.mem.Allocator, terms: *TermPool) !FormulaPool {
        var p = FormulaPool{
            .allocator = allocator,
            .terms = terms,
        };
        try p.tags.append(allocator, .false_);
        try p.a.append(allocator, 0);
        try p.b.append(allocator, 0);
        try p.pred.append(allocator, 0);
        try p.atom_arg_start.append(allocator, 0);
        try p.atom_arity.append(allocator, 0);

        try p.tags.append(allocator, .true_);
        try p.a.append(allocator, 0);
        try p.b.append(allocator, 0);
        try p.pred.append(allocator, 0);
        try p.atom_arg_start.append(allocator, 0);
        try p.atom_arity.append(allocator, 0);
        return p;
    }

    pub fn deinit(self: *FormulaPool) void {
        self.tags.deinit(self.allocator);
        self.a.deinit(self.allocator);
        self.b.deinit(self.allocator);
        self.pred.deinit(self.allocator);
        self.atom_arg_start.deinit(self.allocator);
        self.atom_arity.deinit(self.allocator);
        self.atom_args.deinit(self.allocator);
        self.* = undefined;
    }

    fn push(self: *FormulaPool, tag: FormulaTag, aa: u32, bb: u32) !FormulaId {
        const id = FormulaId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, tag);
        try self.a.append(self.allocator, aa);
        try self.b.append(self.allocator, bb);
        try self.pred.append(self.allocator, 0);
        try self.atom_arg_start.append(self.allocator, 0);
        try self.atom_arity.append(self.allocator, 0);
        return id;
    }

    pub fn mkAtom(self: *FormulaPool, pred_name: []const u8, args: []const TermId) !FormulaId {
        const sid = try self.terms.interner.intern(pred_name);
        const start: u32 = @intCast(self.atom_args.items.len);
        try self.atom_args.appendSlice(self.allocator, args);
        const id = FormulaId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, .atom);
        try self.a.append(self.allocator, 0);
        try self.b.append(self.allocator, 0);
        try self.pred.append(self.allocator, sid.index());
        try self.atom_arg_start.append(self.allocator, start);
        try self.atom_arity.append(self.allocator, @intCast(args.len));
        return id;
    }

    pub fn mkEq(self: *FormulaPool, l: TermId, r: TermId) !FormulaId {
        return self.push(.eq, l.index(), r.index());
    }

    pub fn mkNot(self: *FormulaPool, f: FormulaId) !FormulaId {
        if (f == .false_) return .true_;
        if (f == .true_) return .false_;
        return self.push(.not, f.index(), 0);
    }

    pub fn mkAnd(self: *FormulaPool, l: FormulaId, r: FormulaId) !FormulaId {
        if (l == .false_ or r == .false_) return .false_;
        if (l == .true_) return r;
        if (r == .true_) return l;
        return self.push(.and_, l.index(), r.index());
    }

    pub fn mkOr(self: *FormulaPool, l: FormulaId, r: FormulaId) !FormulaId {
        if (l == .true_ or r == .true_) return .true_;
        if (l == .false_) return r;
        if (r == .false_) return l;
        return self.push(.or_, l.index(), r.index());
    }

    pub fn mkImplies(self: *FormulaPool, l: FormulaId, r: FormulaId) !FormulaId {
        return self.push(.implies, l.index(), r.index());
    }

    pub fn mkForall(self: *FormulaPool, var_term: TermId, body: FormulaId) !FormulaId {
        std.debug.assert(self.terms.isVar(var_term));
        return self.push(.forall, var_term.index(), body.index());
    }

    pub fn mkExists(self: *FormulaPool, var_term: TermId, body: FormulaId) !FormulaId {
        std.debug.assert(self.terms.isVar(var_term));
        return self.push(.exists, var_term.index(), body.index());
    }

    pub fn tagOf(self: *const FormulaPool, f: FormulaId) FormulaTag {
        return self.tags.items[f.index()];
    }

    pub fn left(self: *const FormulaPool, f: FormulaId) FormulaId {
        return FormulaId.fromIndex(self.a.items[f.index()]);
    }

    pub fn right(self: *const FormulaPool, f: FormulaId) FormulaId {
        return FormulaId.fromIndex(self.b.items[f.index()]);
    }

    pub fn atomArgs(self: *const FormulaPool, f: FormulaId) []const TermId {
        const st = self.atom_arg_start.items[f.index()];
        const ar = self.atom_arity.items[f.index()];
        return self.atom_args.items[st .. st + ar];
    }

    pub fn atomPred(self: *const FormulaPool, f: FormulaId) []const u8 {
        return self.terms.interner.get(SymbolId.fromIndex(self.pred.items[f.index()]));
    }

    pub fn eqLeft(self: *const FormulaPool, f: FormulaId) TermId {
        return TermId.fromIndex(self.a.items[f.index()]);
    }

    pub fn eqRight(self: *const FormulaPool, f: FormulaId) TermId {
        return TermId.fromIndex(self.b.items[f.index()]);
    }

    pub fn binderVar(self: *const FormulaPool, f: FormulaId) TermId {
        return TermId.fromIndex(self.a.items[f.index()]);
    }

    pub fn binderBody(self: *const FormulaPool, f: FormulaId) FormulaId {
        return FormulaId.fromIndex(self.b.items[f.index()]);
    }

    /// Free variables of a formula (TermIds of free vars that are not bound by enclosing quantifiers).
    pub fn freeVars(self: *const FormulaPool, f: FormulaId, out: *std.ArrayList(TermId)) !void {
        var bound: std.AutoHashMapUnmanaged(u32, void) = .{};
        defer bound.deinit(self.allocator);
        try freeVarsRec(self, f, &bound, out);
    }

    fn freeVarsRec(
        self: *const FormulaPool,
        f: FormulaId,
        bound: *std.AutoHashMapUnmanaged(u32, void),
        out: *std.ArrayList(TermId),
    ) !void {
        switch (self.tagOf(f)) {
            .false_, .true_ => {},
            .atom => {
                for (self.atomArgs(f)) |t| try freeVarsTerm(self.terms, t, bound, out);
            },
            .eq => {
                try freeVarsTerm(self.terms, self.eqLeft(f), bound, out);
                try freeVarsTerm(self.terms, self.eqRight(f), bound, out);
            },
            .not => try freeVarsRec(self, self.left(f), bound, out),
            .and_, .or_, .implies => {
                try freeVarsRec(self, self.left(f), bound, out);
                try freeVarsRec(self, self.right(f), bound, out);
            },
            .forall, .exists => {
                const v = self.binderVar(f);
                const k = v.index();
                const already = bound.contains(k);
                if (!already) try bound.put(self.allocator, k, {});
                try freeVarsRec(self, self.binderBody(f), bound, out);
                if (!already) _ = bound.remove(k);
            },
        }
    }

    fn freeVarsTerm(
        pool: *const TermPool,
        t: TermId,
        bound: *std.AutoHashMapUnmanaged(u32, void),
        out: *std.ArrayList(TermId),
    ) !void {
        switch (pool.tag(t)) {
            .variable => {
                if (!bound.contains(t.index())) {
                    for (out.items) |e| if (e == t) return;
                    try out.append(pool.allocator, t);
                }
            },
            .constant => {},
            .func => {
                for (pool.argsOf(t)) |a| try freeVarsTerm(pool, a, bound, out);
            },
        }
    }

    /// Capture-avoiding substitution of free var `from` by term `to` in formula.
    pub fn substFree(self: *FormulaPool, f: FormulaId, from: TermId, to: TermId) !FormulaId {
        return substFreeRec(self, f, from, to);
    }

    fn substFreeRec(self: *FormulaPool, f: FormulaId, from: TermId, to: TermId) !FormulaId {
        switch (self.tagOf(f)) {
            .false_ => return .false_,
            .true_ => return .true_,
            .atom => {
                const args = self.atomArgs(f);
                var buf: [8]TermId = undefined;
                if (args.len > buf.len) return error.TooManyArgs;
                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    buf[i] = try substTerm(self.terms, args[i], from, to);
                }
                return try self.mkAtom(self.atomPred(f), buf[0..args.len]);
            },
            .eq => {
                const l = try substTerm(self.terms, self.eqLeft(f), from, to);
                const r = try substTerm(self.terms, self.eqRight(f), from, to);
                return try self.mkEq(l, r);
            },
            .not => return try self.mkNot(try substFreeRec(self, self.left(f), from, to)),
            .and_ => return try self.mkAnd(
                try substFreeRec(self, self.left(f), from, to),
                try substFreeRec(self, self.right(f), from, to),
            ),
            .or_ => return try self.mkOr(
                try substFreeRec(self, self.left(f), from, to),
                try substFreeRec(self, self.right(f), from, to),
            ),
            .implies => return try self.mkImplies(
                try substFreeRec(self, self.left(f), from, to),
                try substFreeRec(self, self.right(f), from, to),
            ),
            .forall, .exists => {
                const v = self.binderVar(f);
                if (v == from) {
                    // Shadowed: no substitution under binder
                    return f;
                }
                const body = try substFreeRec(self, self.binderBody(f), from, to);
                if (self.tagOf(f) == .forall) return try self.mkForall(v, body);
                return try self.mkExists(v, body);
            },
        }
    }

    fn substTerm(pool: *TermPool, t: TermId, from: TermId, to: TermId) !TermId {
        if (t == from) return to;
        switch (pool.tag(t)) {
            .variable, .constant => return t,
            .func => {
                const args = pool.argsOf(t);
                var buf: [8]TermId = undefined;
                if (args.len > buf.len) return error.TooManyArgs;
                var changed = false;
                var i: usize = 0;
                while (i < args.len) : (i += 1) {
                    buf[i] = try substTerm(pool, args[i], from, to);
                    if (buf[i] != args[i]) changed = true;
                }
                if (!changed) return t;
                return try pool.mkFunc(pool.nameOf(t), buf[0..args.len]);
            },
        }
    }

    /// Alpha-equivalence: same structure, binders renamed consistently.
    pub fn alphaEq(self: *const FormulaPool, a: FormulaId, b: FormulaId) bool {
        var map_ab: std.AutoHashMapUnmanaged(u32, u32) = .{};
        var map_ba: std.AutoHashMapUnmanaged(u32, u32) = .{};
        defer map_ab.deinit(self.allocator);
        defer map_ba.deinit(self.allocator);
        return alphaEqRec(self, a, b, &map_ab, &map_ba) catch false;
    }

    fn alphaEqRec(
        self: *const FormulaPool,
        a: FormulaId,
        b: FormulaId,
        map_ab: *std.AutoHashMapUnmanaged(u32, u32),
        map_ba: *std.AutoHashMapUnmanaged(u32, u32),
    ) !bool {
        if (self.tagOf(a) != self.tagOf(b)) return false;
        switch (self.tagOf(a)) {
            .false_, .true_ => return true,
            .atom => {
                if (!std.mem.eql(u8, self.atomPred(a), self.atomPred(b))) return false;
                const aa = self.atomArgs(a);
                const bb = self.atomArgs(b);
                if (aa.len != bb.len) return false;
                for (aa, bb) |ta, tb| {
                    if (!try alphaEqTerm(self.terms, ta, tb, map_ab, map_ba)) return false;
                }
                return true;
            },
            .eq => {
                return (try alphaEqTerm(self.terms, self.eqLeft(a), self.eqLeft(b), map_ab, map_ba)) and
                    (try alphaEqTerm(self.terms, self.eqRight(a), self.eqRight(b), map_ab, map_ba));
            },
            .not => return try alphaEqRec(self, self.left(a), self.left(b), map_ab, map_ba),
            .and_, .or_, .implies => {
                return (try alphaEqRec(self, self.left(a), self.left(b), map_ab, map_ba)) and
                    (try alphaEqRec(self, self.right(a), self.right(b), map_ab, map_ba));
            },
            .forall, .exists => {
                const va = self.binderVar(a).index();
                const vb = self.binderVar(b).index();
                // Temporarily map binders
                const old_ab = map_ab.fetchPut(self.allocator, va, vb) catch return false;
                const old_ba = map_ba.fetchPut(self.allocator, vb, va) catch return false;
                const ok = try alphaEqRec(self, self.binderBody(a), self.binderBody(b), map_ab, map_ba);
                // restore
                if (old_ab) |e| {
                    try map_ab.put(self.allocator, va, e.value);
                } else _ = map_ab.remove(va);
                if (old_ba) |e| {
                    try map_ba.put(self.allocator, vb, e.value);
                } else _ = map_ba.remove(vb);
                return ok;
            },
        }
    }

    fn alphaEqTerm(
        pool: *const TermPool,
        a: TermId,
        b: TermId,
        map_ab: *std.AutoHashMapUnmanaged(u32, u32),
        map_ba: *std.AutoHashMapUnmanaged(u32, u32),
    ) !bool {
        if (pool.tag(a) != pool.tag(b)) return false;
        switch (pool.tag(a)) {
            .variable => {
                const ia = a.index();
                const ib = b.index();
                if (map_ab.get(ia)) |mapped| return mapped == ib;
                if (map_ba.contains(ib)) return false;
                // Free: must be identical TermId
                return ia == ib;
            },
            .constant => return std.mem.eql(u8, pool.rawNameOf(a), pool.rawNameOf(b)),
            .func => {
                if (!std.mem.eql(u8, pool.nameOf(a), pool.nameOf(b))) return false;
                const aa = pool.argsOf(a);
                const bb = pool.argsOf(b);
                if (aa.len != bb.len) return false;
                for (aa, bb) |ta, tb| {
                    if (!try alphaEqTerm(pool, ta, tb, map_ab, map_ba)) return false;
                }
                return true;
            },
        }
    }
};

test "term pool fresh vars distinct" {
    var tp = TermPool.init(std.testing.allocator);
    defer tp.deinit();
    const x1 = try tp.mkVar("x");
    const x2 = try tp.mkVar("x");
    try std.testing.expect(x1 != x2);
    try std.testing.expectEqualStrings("x", tp.printName(x1));
    try std.testing.expectEqualStrings("x", tp.printName(x2));
    const a = try tp.mkConst("a");
    const a2 = try tp.mkConst("a");
    try std.testing.expect(a == a2);
}

test "alpha eq binders" {
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    var fpool = try FormulaPool.init(std.testing.allocator, &terms);
    defer fpool.deinit();

    const x = try terms.mkVar("x");
    const y = try terms.mkVar("y");
    const px = try fpool.mkAtom("P", &.{x});
    const py = try fpool.mkAtom("P", &.{y});
    const ax = try fpool.mkForall(x, px);
    const ay = try fpool.mkForall(y, py);
    try std.testing.expect(fpool.alphaEq(ax, ay));

    const qx = try fpool.mkAtom("Q", &.{x});
    const axq = try fpool.mkForall(x, qx);
    try std.testing.expect(!fpool.alphaEq(ax, axq));
}

test "env push pop restore" {
    var terms = TermPool.init(std.testing.allocator);
    defer terms.deinit();
    const x = try terms.mkVar("x");
    var env = Env.init(std.testing.allocator);
    defer env.deinit();
    try env.push(x, 1);
    try env.push(x, 2);
    try std.testing.expect(env.get(x).? == 2);
    env.pop();
    try std.testing.expect(env.get(x).? == 1);
    env.pop();
    try std.testing.expect(env.get(x) == null);
}
