//! Description logic EL — polynomial subsumption via completion rules.
//!
//! EL concepts: atomic names, ⊤, conjunction C ⊓ D, existential restriction
//! ∃r.C. TBox axioms C ⊑ D (general concept inclusions). Subsumption is
//! decided by normalization to the four EL normal forms
//!
//!   A ⊑ B      A₁ ⊓ A₂ ⊑ B      A ⊑ ∃r.B      ∃r.A ⊑ B
//!
//! (fresh names for complex subconcepts), then the standard completion
//! algorithm: saturate S(A) ∋ B ("A ⊑ B derived") and R(r) ∋ (A,B)
//! ("A ⊑ ∃r.B derived") under the completion rules until fixpoint. This is
//! the classification core of EL / EL++ (Baader–Brandt–Lutz), sound and
//! complete for subsumption between named concepts.

const std = @import("std");

pub const Concept = union(enum) {
    top,
    name: u32,
    conj: [2]*const Concept,
    exists: struct { role: u32, filler: *const Concept },
};

pub const Axiom = struct {
    sub: *const Concept,
    sup: *const Concept,
};

pub const Builder = struct {
    arena: std.heap.ArenaAllocator,

    pub fn init(allocator: std.mem.Allocator) Builder {
        return .{ .arena = std.heap.ArenaAllocator.init(allocator) };
    }
    pub fn deinit(self: *Builder) void {
        self.arena.deinit();
    }
    fn mk(self: *Builder, c: Concept) *const Concept {
        const p = self.arena.allocator().create(Concept) catch @panic("oom");
        p.* = c;
        return p;
    }
    pub fn top(self: *Builder) *const Concept {
        return self.mk(.top);
    }
    pub fn name(self: *Builder, i: u32) *const Concept {
        return self.mk(.{ .name = i });
    }
    pub fn conj(self: *Builder, a: *const Concept, b: *const Concept) *const Concept {
        return self.mk(.{ .conj = .{ a, b } });
    }
    pub fn exists(self: *Builder, role: u32, filler: *const Concept) *const Concept {
        return self.mk(.{ .exists = .{ .role = role, .filler = filler } });
    }
};

const NormAxiom = union(enum) {
    /// A ⊑ B
    sub_name: [2]u32,
    /// A1 ⊓ A2 ⊑ B
    sub_conj: [3]u32,
    /// A ⊑ ∃r.B
    sub_exists: [3]u32, // A, r, B
    /// ∃r.A ⊑ B
    exists_sub: [3]u32, // r, A, B
};

const Normalizer = struct {
    allocator: std.mem.Allocator,
    axioms: std.ArrayList(NormAxiom) = .empty,
    next_name: u32,
    top_name: u32,

    fn deinit(self: *Normalizer) void {
        self.axioms.deinit(self.allocator);
    }

    fn fresh(self: *Normalizer) u32 {
        const n = self.next_name;
        self.next_name += 1;
        return n;
    }

    /// Name a concept: returns an atomic name N with N ≡ C enforced in the
    /// direction(s) needed. For EL completeness both directions are added.
    fn nameOf(self: *Normalizer, c: *const Concept) error{OutOfMemory}!u32 {
        switch (c.*) {
            .top => return self.top_name,
            .name => |i| return i,
            .conj => |p| {
                const a = try self.nameOf(p[0]);
                const b = try self.nameOf(p[1]);
                const n = self.fresh();
                // A ⊓ B ⊑ N and N ⊑ A, N ⊑ B.
                try self.axioms.append(self.allocator, .{ .sub_conj = .{ a, b, n } });
                try self.axioms.append(self.allocator, .{ .sub_name = .{ n, a } });
                try self.axioms.append(self.allocator, .{ .sub_name = .{ n, b } });
                return n;
            },
            .exists => |e| {
                const f = try self.nameOf(e.filler);
                const n = self.fresh();
                // N ⊑ ∃r.F and ∃r.F ⊑ N.
                try self.axioms.append(self.allocator, .{ .sub_exists = .{ n, e.role, f } });
                try self.axioms.append(self.allocator, .{ .exists_sub = .{ e.role, f, n } });
                return n;
            },
        }
    }
};

pub const Tbox = struct {
    allocator: std.mem.Allocator,
    norm: std.ArrayList(NormAxiom) = .empty,
    num_names: u32,
    num_roles: u32,
    top_name: u32,

    pub fn deinit(self: *Tbox) void {
        self.norm.deinit(self.allocator);
        self.* = undefined;
    }
};

/// Normalize a general EL TBox. `num_names`/`num_roles` bound the input ids.
pub fn normalize(
    allocator: std.mem.Allocator,
    axioms: []const Axiom,
    num_names: u32,
    num_roles: u32,
) !Tbox {
    var nz = Normalizer{
        .allocator = allocator,
        .next_name = num_names + 1, // reserve one slot for ⊤'s name
        .top_name = num_names,
    };
    errdefer nz.deinit();
    for (axioms) |ax| {
        const a = try nz.nameOf(ax.sub);
        const b = try nz.nameOf(ax.sup);
        try nz.axioms.append(allocator, .{ .sub_name = .{ a, b } });
    }
    return .{
        .allocator = allocator,
        .norm = nz.axioms,
        .num_names = nz.next_name,
        .num_roles = num_roles,
        .top_name = nz.top_name,
    };
}

pub const Classification = struct {
    allocator: std.mem.Allocator,
    n: u32,
    /// s[a*n + b] — derived a ⊑ b.
    s: []bool,

    pub fn deinit(self: *Classification) void {
        self.allocator.free(self.s);
        self.* = undefined;
    }

    pub fn subsumes(self: *const Classification, sub: u32, sup: u32) bool {
        return self.s[sub * self.n + sup];
    }
};

/// Saturate the completion rules; result answers A ⊑? B for named concepts.
pub fn classify(allocator: std.mem.Allocator, tbox: *const Tbox) !Classification {
    const n = tbox.num_names;
    const s = try allocator.alloc(bool, n * n);
    errdefer allocator.free(s);
    @memset(s, false);
    // Init: A ⊑ A, A ⊑ ⊤.
    for (0..n) |a| {
        s[a * n + a] = true;
        s[a * n + tbox.top_name] = true;
    }
    // R(r) as adjacency: r_edges[r*n*n + a*n + b].
    const r_edges = try allocator.alloc(bool, tbox.num_roles * n * n);
    defer allocator.free(r_edges);
    @memset(r_edges, false);

    var changed = true;
    while (changed) {
        changed = false;
        for (tbox.norm.items) |ax| {
            switch (ax) {
                .sub_name => |p| {
                    // A' ⊑ B: for every X with X ⊑ A', add X ⊑ B.
                    for (0..n) |x| {
                        if (s[x * n + p[0]] and !s[x * n + p[1]]) {
                            s[x * n + p[1]] = true;
                            changed = true;
                        }
                    }
                },
                .sub_conj => |p| {
                    for (0..n) |x| {
                        if (s[x * n + p[0]] and s[x * n + p[1]] and !s[x * n + p[2]]) {
                            s[x * n + p[2]] = true;
                            changed = true;
                        }
                    }
                },
                .sub_exists => |p| {
                    // A ⊑ ∃r.B: for X ⊑ A, add edge X -r-> B.
                    for (0..n) |x| {
                        if (s[x * n + p[0]]) {
                            const idx = p[1] * n * n + x * n + p[2];
                            if (!r_edges[idx]) {
                                r_edges[idx] = true;
                                changed = true;
                            }
                        }
                    }
                },
                .exists_sub => |p| {
                    // ∃r.A ⊑ B: for edge X -r-> Y with Y ⊑ A, add X ⊑ B.
                    for (0..n) |x| {
                        for (0..n) |y| {
                            if (r_edges[p[0] * n * n + x * n + y] and s[y * n + p[1]] and !s[x * n + p[2]]) {
                                s[x * n + p[2]] = true;
                                changed = true;
                            }
                        }
                    }
                },
            }
        }
    }
    return .{ .allocator = allocator, .n = n, .s = s };
}

/// Convenience: does the TBox entail name_a ⊑ name_b?
pub fn subsumed(allocator: std.mem.Allocator, tbox: *const Tbox, a: u32, b: u32) !bool {
    var cls = try classify(allocator, tbox);
    defer cls.deinit();
    return cls.subsumes(a, b);
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "el: chained existential propagation" {
    // A ⊑ ∃r.B, B ⊑ C, ∃r.C ⊑ D  ⟹  A ⊑ D.
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const A = 0;
    const B = 1;
    const C = 2;
    const D = 3;
    const r = 0;
    const axioms = [_]Axiom{
        .{ .sub = b.name(A), .sup = b.exists(r, b.name(B)) },
        .{ .sub = b.name(B), .sup = b.name(C) },
        .{ .sub = b.exists(r, b.name(C)), .sup = b.name(D) },
    };
    var tb = try normalize(testing.allocator, &axioms, 4, 1);
    defer tb.deinit();
    try testing.expect(try subsumed(testing.allocator, &tb, A, D));
    // No spurious closures.
    try testing.expect(!try subsumed(testing.allocator, &tb, D, A));
    try testing.expect(!try subsumed(testing.allocator, &tb, C, B));
    try testing.expect(!try subsumed(testing.allocator, &tb, A, B));
}

test "el: pericarditis canon (Baader et al. style)" {
    // Pericarditis ⊑ Inflammation ⊓ ∃loc.Pericardium
    // Inflammation ⊑ Disease
    // Disease ⊓ ∃loc.Heart... simplified: Pericardium ⊑ ∃partof.Heart? EL chain:
    // Use: Disease ⊓ ∃loc.Pericardium ⊑ HeartDisease.
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const Pericarditis = 0;
    const Inflammation = 1;
    const Disease = 2;
    const Pericardium = 3;
    const HeartDisease = 4;
    const loc = 0;
    const axioms = [_]Axiom{
        .{ .sub = b.name(Pericarditis), .sup = b.conj(b.name(Inflammation), b.exists(loc, b.name(Pericardium))) },
        .{ .sub = b.name(Inflammation), .sup = b.name(Disease) },
        .{ .sub = b.conj(b.name(Disease), b.exists(loc, b.name(Pericardium))), .sup = b.name(HeartDisease) },
    };
    var tb = try normalize(testing.allocator, &axioms, 5, 1);
    defer tb.deinit();
    var cls = try classify(testing.allocator, &tb);
    defer cls.deinit();
    // Full expected closure among named concepts:
    try testing.expect(cls.subsumes(Pericarditis, Inflammation));
    try testing.expect(cls.subsumes(Pericarditis, Disease));
    try testing.expect(cls.subsumes(Pericarditis, HeartDisease));
    try testing.expect(cls.subsumes(Inflammation, Disease));
    // And nothing else between distinct named concepts:
    try testing.expect(!cls.subsumes(Inflammation, HeartDisease));
    try testing.expect(!cls.subsumes(Disease, HeartDisease));
    try testing.expect(!cls.subsumes(HeartDisease, Disease));
    try testing.expect(!cls.subsumes(Pericardium, Disease));
    try testing.expect(!cls.subsumes(Disease, Inflammation));
}

test "el: top and reflexivity" {
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const A = 0;
    const axioms = [_]Axiom{
        .{ .sub = b.name(A), .sup = b.top() },
    };
    var tb = try normalize(testing.allocator, &axioms, 1, 1);
    defer tb.deinit();
    var cls = try classify(testing.allocator, &tb);
    defer cls.deinit();
    try testing.expect(cls.subsumes(A, A));
    try testing.expect(cls.subsumes(A, tb.top_name));
}

test "el: conjunction both directions" {
    // A ⊑ B ⊓ C gives A ⊑ B and A ⊑ C; B ⊓ C ⊑ D with A ⊑ B, A ⊑ C gives A ⊑ D.
    var b = Builder.init(testing.allocator);
    defer b.deinit();
    const A = 0;
    const B = 1;
    const C = 2;
    const D = 3;
    const axioms = [_]Axiom{
        .{ .sub = b.name(A), .sup = b.conj(b.name(B), b.name(C)) },
        .{ .sub = b.conj(b.name(B), b.name(C)), .sup = b.name(D) },
    };
    var tb = try normalize(testing.allocator, &axioms, 4, 0);
    defer tb.deinit();
    var cls = try classify(testing.allocator, &tb);
    defer cls.deinit();
    try testing.expect(cls.subsumes(A, B));
    try testing.expect(cls.subsumes(A, C));
    try testing.expect(cls.subsumes(A, D));
    try testing.expect(!cls.subsumes(B, D));
}
