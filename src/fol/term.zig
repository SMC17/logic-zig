//! First-order terms and atomic formulas (arena / pool based).

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
    variable,
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
    eq, // t1 = t2
};

pub const TermPool = struct {
    allocator: std.mem.Allocator,
    tags: std.ArrayList(TermTag) = .empty,
    /// For var/const: symbol; for func: function symbol.
    sym: std.ArrayList(u32) = .empty,
    /// For func: start index into arg_data; arity in arity list.
    arg_start: std.ArrayList(u32) = .empty,
    arity: std.ArrayList(u16) = .empty,
    arg_data: std.ArrayList(TermId) = .empty,
    interner: Interner,
    /// name → TermId for variables (same name = same id, required for occurs).
    var_by_name: std.StringHashMapUnmanaged(TermId) = .{},
    /// name → TermId for constants.
    const_by_name: std.StringHashMapUnmanaged(TermId) = .{},

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
        self.var_by_name.deinit(self.allocator);
        self.const_by_name.deinit(self.allocator);
        self.interner.deinit();
        self.* = undefined;
    }

    pub fn mkVar(self: *TermPool, name: []const u8) !TermId {
        if (self.var_by_name.get(name)) |id| return id;
        const sid = try self.interner.intern(name);
        const id = TermId.fromIndex(@intCast(self.tags.items.len));
        try self.tags.append(self.allocator, .variable);
        try self.sym.append(self.allocator, sid.index());
        try self.arg_start.append(self.allocator, 0);
        try self.arity.append(self.allocator, 0);
        // Key must outlive: use interned bytes.
        const key = self.interner.get(sid);
        try self.var_by_name.put(self.allocator, key, id);
        return id;
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

    pub fn nameOf(self: *const TermPool, t: TermId) []const u8 {
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
};

pub const FormulaPool = struct {
    allocator: std.mem.Allocator,
    terms: *TermPool,
    tags: std.ArrayList(FormulaTag) = .empty,
    a: std.ArrayList(u32) = .empty,
    b: std.ArrayList(u32) = .empty,
    /// For atoms: predicate symbol + args in atom_args
    pred: std.ArrayList(u32) = .empty,
    atom_arg_start: std.ArrayList(u32) = .empty,
    atom_arity: std.ArrayList(u16) = .empty,
    atom_args: std.ArrayList(TermId) = .empty,

    pub fn init(allocator: std.mem.Allocator, terms: *TermPool) !FormulaPool {
        var p = FormulaPool{
            .allocator = allocator,
            .terms = terms,
        };
        // false, true
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
};

test "term pool" {
    var tp = TermPool.init(std.testing.allocator);
    defer tp.deinit();
    const x = try tp.mkVar("x");
    const a = try tp.mkConst("a");
    const fx = try tp.mkFunc("f", &.{x});
    try std.testing.expect(tp.isVar(x));
    try std.testing.expect(tp.tag(fx) == .func);
    try std.testing.expectEqualStrings("a", tp.nameOf(a));
}
