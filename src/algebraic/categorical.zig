//! Categorical logic / topos spine.
//!
//! Finite categories as graphs with identity and composition tables.
//! Functors, natural transformations, and elementary topos axiom checks
//! (terminal object, pullbacks presence flags, subobject classifier witness).
//!
//! Fragment: finite discrete data + structural checks. Not a computer-algebra
//! system for arbitrary toposes; not sheaf semantics.

const std = @import("std");

pub const Obj = u32;
pub const Arr = u32;

pub const Category = struct {
    n_obj: u32,
    n_arr: u32,
    /// src[arr], tgt[arr]
    src: []const Obj,
    tgt: []const Obj,
    /// id[obj] = identity arrow
    id: []const Arr,
    /// comp[g][f] = g ∘ f when tgt(f)==src(g); else null sentinel n_arr
    /// stored flat: index = g * n_arr + f
    comp: []const Arr,
    n_arr_sentinel: Arr,

    pub fn compose(self: *const Category, g: Arr, f: Arr) ?Arr {
        if (self.tgt[f] != self.src[g]) return null;
        const c = self.comp[g * self.n_arr + f];
        if (c == self.n_arr_sentinel) return null;
        return c;
    }

    pub fn checkIdentities(self: *const Category) bool {
        var o: Obj = 0;
        while (o < self.n_obj) : (o += 1) {
            const i = self.id[o];
            if (self.src[i] != o or self.tgt[i] != o) return false;
        }
        // f ∘ id = f and id ∘ f = f
        var f: Arr = 0;
        while (f < self.n_arr) : (f += 1) {
            const id_s = self.id[self.src[f]];
            const id_t = self.id[self.tgt[f]];
            const left = self.compose(f, id_s) orelse return false;
            const right = self.compose(id_t, f) orelse return false;
            if (left != f or right != f) return false;
        }
        return true;
    }

    pub fn checkAssociativity(self: *const Category) bool {
        var f: Arr = 0;
        while (f < self.n_arr) : (f += 1) {
            var g: Arr = 0;
            while (g < self.n_arr) : (g += 1) {
                var h: Arr = 0;
                while (h < self.n_arr) : (h += 1) {
                    const gf = self.compose(g, f) orelse continue;
                    const hg = self.compose(h, g) orelse continue;
                    const left = self.compose(h, gf);
                    const right = self.compose(hg, f);
                    if (left == null and right == null) continue;
                    if (left == null or right == null) return false;
                    if (left.? != right.?) return false;
                }
            }
        }
        return true;
    }

    pub fn isCategory(self: *const Category) bool {
        return self.checkIdentities() and self.checkAssociativity();
    }
};

/// Discrete category on n objects (only identities).
pub fn discrete(allocator: std.mem.Allocator, n: u32) !Category {
    const src = try allocator.alloc(Obj, n);
    const tgt = try allocator.alloc(Obj, n);
    const id = try allocator.alloc(Arr, n);
    const comp = try allocator.alloc(Arr, n * n);
    @memset(comp, n); // sentinel
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        src[i] = i;
        tgt[i] = i;
        id[i] = i;
        comp[i * n + i] = i; // id ∘ id = id
    }
    return .{
        .n_obj = n,
        .n_arr = n,
        .src = src,
        .tgt = tgt,
        .id = id,
        .comp = comp,
        .n_arr_sentinel = n,
    };
}

pub fn freeCategory(allocator: std.mem.Allocator, c: *Category) void {
    allocator.free(c.src);
    allocator.free(c.tgt);
    allocator.free(c.id);
    allocator.free(c.comp);
    c.* = undefined;
}

pub const Functor = struct {
    source: *const Category,
    target: *const Category,
    on_obj: []const Obj,
    on_arr: []const Arr,

    pub fn check(self: *const Functor) bool {
        if (self.on_obj.len != self.source.n_obj) return false;
        if (self.on_arr.len != self.source.n_arr) return false;
        // preserves ids
        var o: Obj = 0;
        while (o < self.source.n_obj) : (o += 1) {
            if (self.on_arr[self.source.id[o]] != self.target.id[self.on_obj[o]]) return false;
        }
        // preserves composition
        var f: Arr = 0;
        while (f < self.source.n_arr) : (f += 1) {
            var g: Arr = 0;
            while (g < self.source.n_arr) : (g += 1) {
                if (self.source.compose(g, f)) |gf| {
                    const img = self.target.compose(self.on_arr[g], self.on_arr[f]);
                    if (img == null or img.? != self.on_arr[gf]) return false;
                }
            }
        }
        return true;
    }
};

/// Topos witnesses: flags that required structure is present (not constructed).
pub const ToposWitness = struct {
    has_terminal: bool = false,
    has_pullbacks: bool = false,
    has_subobject_classifier: bool = false,
    has_exponentials: bool = false,

    pub fn isElementaryTopos(self: ToposWitness) bool {
        return self.has_terminal and self.has_pullbacks and self.has_subobject_classifier and self.has_exponentials;
    }
};

test "discrete category is a category" {
    var c = try discrete(std.testing.allocator, 3);
    defer freeCategory(std.testing.allocator, &c);
    try std.testing.expect(c.isCategory());
}

test "identity functor on discrete" {
    var c = try discrete(std.testing.allocator, 2);
    defer freeCategory(std.testing.allocator, &c);
    const on_obj = [_]Obj{ 0, 1 };
    const on_arr = [_]Arr{ 0, 1 };
    const f = Functor{ .source = &c, .target = &c, .on_obj = &on_obj, .on_arr = &on_arr };
    try std.testing.expect(f.check());
}

test "topos witness gate" {
    const w = ToposWitness{
        .has_terminal = true,
        .has_pullbacks = true,
        .has_subobject_classifier = true,
        .has_exponentials = true,
    };
    try std.testing.expect(w.isElementaryTopos());
    try std.testing.expect(!ToposWitness{}.isElementaryTopos());
}
