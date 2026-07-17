//! Hash-consed propositional expression pool (SoA layout).
//!
//! Reserved IDs: 0 = false, 1 = true. All other nodes are unique under
//! structural equality via a hash-cons table.

const std = @import("std");
const lit_mod = @import("../core/lit.zig");
const interner_mod = @import("../core/interner.zig");

pub const Var = lit_mod.Var;
pub const Lit = lit_mod.Lit;
pub const SymbolId = interner_mod.SymbolId;
pub const Interner = interner_mod.Interner;

pub const ExprId = enum(u32) {
    false_ = 0,
    true_ = 1,
    _,

    pub fn index(self: ExprId) u32 {
        return @intFromEnum(self);
    }

    pub fn fromIndex(i: u32) ExprId {
        return @enumFromInt(i);
    }

    pub fn isConst(self: ExprId) bool {
        return self == .false_ or self == .true_;
    }

    pub fn asBool(self: ExprId) ?bool {
        return switch (self) {
            .false_ => false,
            .true_ => true,
            else => null,
        };
    }
};

pub const ExprTag = enum(u8) {
    false_,
    true_,
    var_,
    not,
    and_,
    or_,
    xor,
    implies,
    iff,
};

const HashKey = struct {
    tag: ExprTag,
    a: u32,
    b: u32,

    pub fn hash(self: HashKey) u64 {
        var h = std.hash.Wyhash.init(0x6c6f676963);
        h.update(std.mem.asBytes(&self.tag));
        h.update(std.mem.asBytes(&self.a));
        h.update(std.mem.asBytes(&self.b));
        return h.final();
    }

    pub fn eql(x: HashKey, y: HashKey) bool {
        return x.tag == y.tag and x.a == y.a and x.b == y.b;
    }
};

const HashCtx = struct {
    pub fn hash(_: HashCtx, k: HashKey) u64 {
        return k.hash();
    }
    pub fn eql(_: HashCtx, a: HashKey, b: HashKey) bool {
        return a.eql(b);
    }
};

pub const ExprPool = struct {
    allocator: std.mem.Allocator,
    tags: std.ArrayList(ExprTag) = .empty,
    a: std.ArrayList(u32) = .empty,
    b: std.ArrayList(u32) = .empty,
    /// Variable symbol for var_ nodes (SymbolId as u32); unused otherwise.
    var_sym: std.ArrayList(u32) = .empty,
    table: std.HashMapUnmanaged(HashKey, ExprId, HashCtx, 80) = .{},
    interner: Interner,
    /// Maps SymbolId → Var for named propositional variables.
    sym_to_var: std.AutoHashMapUnmanaged(u32, u32) = .{},
    var_to_sym: std.ArrayList(SymbolId) = .empty,

    pub fn init(allocator: std.mem.Allocator) !ExprPool {
        var pool = ExprPool{
            .allocator = allocator,
            .interner = Interner.init(allocator),
        };
        // Reserve false / true.
        try pool.tags.append(allocator, .false_);
        try pool.a.append(allocator, 0);
        try pool.b.append(allocator, 0);
        try pool.var_sym.append(allocator, 0);

        try pool.tags.append(allocator, .true_);
        try pool.a.append(allocator, 0);
        try pool.b.append(allocator, 0);
        try pool.var_sym.append(allocator, 0);
        return pool;
    }

    pub fn deinit(self: *ExprPool) void {
        self.table.deinit(self.allocator);
        self.tags.deinit(self.allocator);
        self.a.deinit(self.allocator);
        self.b.deinit(self.allocator);
        self.var_sym.deinit(self.allocator);
        self.sym_to_var.deinit(self.allocator);
        self.var_to_sym.deinit(self.allocator);
        self.interner.deinit();
        self.* = undefined;
    }

    pub fn numVars(self: *const ExprPool) u32 {
        return @intCast(self.var_to_sym.items.len);
    }

    pub fn tag(self: *const ExprPool, id: ExprId) ExprTag {
        return self.tags.items[id.index()];
    }

    pub fn child(self: *const ExprPool, id: ExprId) ExprId {
        return ExprId.fromIndex(self.a.items[id.index()]);
    }

    pub fn left(self: *const ExprPool, id: ExprId) ExprId {
        return ExprId.fromIndex(self.a.items[id.index()]);
    }

    pub fn right(self: *const ExprPool, id: ExprId) ExprId {
        return ExprId.fromIndex(self.b.items[id.index()]);
    }

    pub fn varOf(self: *const ExprPool, id: ExprId) Var {
        std.debug.assert(self.tag(id) == .var_);
        return Var.fromIndex(self.a.items[id.index()]);
    }

    pub fn varName(self: *const ExprPool, v: Var) []const u8 {
        return self.interner.get(self.var_to_sym.items[v.index()]);
    }

    fn mk(self: *ExprPool, t: ExprTag, aa: u32, bb: u32, vsym: u32) !ExprId {
        const key = HashKey{ .tag = t, .a = aa, .b = bb };
        if (self.table.get(key)) |existing| return existing;

        const id = ExprId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, t);
        try self.a.append(self.allocator, aa);
        try self.b.append(self.allocator, bb);
        try self.var_sym.append(self.allocator, vsym);
        try self.table.put(self.allocator, key, id);
        return id;
    }

    pub fn mkFalse(_: *ExprPool) ExprId {
        return .false_;
    }

    pub fn mkTrue(_: *ExprPool) ExprId {
        return .true_;
    }

    pub fn mkConst(self: *ExprPool, val: bool) ExprId {
        return if (val) self.mkTrue() else self.mkFalse();
    }

    pub fn mkVarNamed(self: *ExprPool, name: []const u8) !ExprId {
        const sid = try self.interner.intern(name);
        if (self.sym_to_var.get(sid.index())) |vi| {
            return try self.mk(.var_, vi, 0, sid.index());
        }
        const vi: u32 = @intCast(self.var_to_sym.items.len);
        try self.var_to_sym.append(self.allocator, sid);
        try self.sym_to_var.put(self.allocator, sid.index(), vi);
        return try self.mk(.var_, vi, 0, sid.index());
    }

    pub fn mkVar(self: *ExprPool, v: Var) !ExprId {
        std.debug.assert(v.index() < self.numVars());
        const sid = self.var_to_sym.items[v.index()];
        return try self.mk(.var_, v.index(), 0, sid.index());
    }

    pub fn mkNot(self: *ExprPool, x: ExprId) !ExprId {
        if (x == .false_) return .true_;
        if (x == .true_) return .false_;
        if (self.tag(x) == .not) return self.child(x);
        return try self.mk(.not, x.index(), 0, 0);
    }

    pub fn mkAnd(self: *ExprPool, l: ExprId, r: ExprId) !ExprId {
        if (l == .false_ or r == .false_) return .false_;
        if (l == .true_) return r;
        if (r == .true_) return l;
        if (l == r) return l;
        // Canonical order for better sharing.
        const lo, const hi = if (l.index() <= r.index()) .{ l, r } else .{ r, l };
        if (self.tag(hi) == .not and self.child(hi) == lo) return .false_;
        return try self.mk(.and_, lo.index(), hi.index(), 0);
    }

    pub fn mkOr(self: *ExprPool, l: ExprId, r: ExprId) !ExprId {
        if (l == .true_ or r == .true_) return .true_;
        if (l == .false_) return r;
        if (r == .false_) return l;
        if (l == r) return l;
        const lo, const hi = if (l.index() <= r.index()) .{ l, r } else .{ r, l };
        if (self.tag(hi) == .not and self.child(hi) == lo) return .true_;
        return try self.mk(.or_, lo.index(), hi.index(), 0);
    }

    pub fn mkXor(self: *ExprPool, l: ExprId, r: ExprId) !ExprId {
        if (l == .false_) return r;
        if (r == .false_) return l;
        if (l == .true_) return try self.mkNot(r);
        if (r == .true_) return try self.mkNot(l);
        if (l == r) return .false_;
        const lo, const hi = if (l.index() <= r.index()) .{ l, r } else .{ r, l };
        return try self.mk(.xor, lo.index(), hi.index(), 0);
    }

    pub fn mkImplies(self: *ExprPool, l: ExprId, r: ExprId) !ExprId {
        if (l == .false_ or r == .true_) return .true_;
        if (l == .true_) return r;
        if (r == .false_) return try self.mkNot(l);
        if (l == r) return .true_;
        return try self.mk(.implies, l.index(), r.index(), 0);
    }

    pub fn mkIff(self: *ExprPool, l: ExprId, r: ExprId) !ExprId {
        if (l == r) return .true_;
        if (l == .true_) return r;
        if (r == .true_) return l;
        if (l == .false_) return try self.mkNot(r);
        if (r == .false_) return try self.mkNot(l);
        const lo, const hi = if (l.index() <= r.index()) .{ l, r } else .{ r, l };
        return try self.mk(.iff, lo.index(), hi.index(), 0);
    }

    /// Evaluate under a total assignment for variables 0..numVars (undef not allowed for full eval).
    pub fn eval(self: *const ExprPool, id: ExprId, assign: []const lit_mod.Value) lit_mod.Value {
        return switch (self.tag(id)) {
            .false_ => .false_,
            .true_ => .true_,
            .var_ => assign[self.a.items[id.index()]],
            .not => switch (self.eval(self.child(id), assign)) {
                .undef => .undef,
                .true_ => .false_,
                .false_ => .true_,
            },
            .and_ => blk: {
                const lv = self.eval(self.left(id), assign);
                const rv = self.eval(self.right(id), assign);
                if (lv == .false_ or rv == .false_) break :blk .false_;
                if (lv == .undef or rv == .undef) break :blk .undef;
                break :blk .true_;
            },
            .or_ => blk: {
                const lv = self.eval(self.left(id), assign);
                const rv = self.eval(self.right(id), assign);
                if (lv == .true_ or rv == .true_) break :blk .true_;
                if (lv == .undef or rv == .undef) break :blk .undef;
                break :blk .false_;
            },
            .xor => blk: {
                const lv = self.eval(self.left(id), assign);
                const rv = self.eval(self.right(id), assign);
                if (lv == .undef or rv == .undef) break :blk .undef;
                break :blk lit_mod.Value.fromBool(lv.isTrue() != rv.isTrue());
            },
            .implies => blk: {
                const lv = self.eval(self.left(id), assign);
                const rv = self.eval(self.right(id), assign);
                if (lv == .false_ or rv == .true_) break :blk .true_;
                if (lv == .undef or rv == .undef) break :blk .undef;
                break :blk .false_;
            },
            .iff => blk: {
                const lv = self.eval(self.left(id), assign);
                const rv = self.eval(self.right(id), assign);
                if (lv == .undef or rv == .undef) break :blk .undef;
                break :blk lit_mod.Value.fromBool(lv == rv);
            },
        };
    }

    /// Structural equality is pointer/ID equality due to hash-cons.
    pub fn eql(_: *const ExprPool, a: ExprId, b: ExprId) bool {
        return a == b;
    }
};

test "hash-cons sharing" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkVarNamed("a");
    const b = try pool.mkVarNamed("b");
    const e1 = try pool.mkAnd(a, b);
    const e2 = try pool.mkAnd(b, a); // ordered
    try std.testing.expect(e1 == e2);
    const n1 = try pool.mkNot(a);
    const n2 = try pool.mkNot(a);
    try std.testing.expect(n1 == n2);
    try std.testing.expect(try pool.mkNot(n1) == a);
}

test "eval basic" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try pool.mkVarNamed("a");
    const b = try pool.mkVarNamed("b");
    const e = try pool.mkImplies(a, b);
    var assign = [_]lit_mod.Value{ .true_, .false_ };
    try std.testing.expect(pool.eval(e, &assign) == .false_);
    assign[1] = .true_;
    try std.testing.expect(pool.eval(e, &assign) == .true_);
}
