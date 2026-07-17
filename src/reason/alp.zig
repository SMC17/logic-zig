//! Abductive logic programming — first-order abduction over the Horn substrate.
//!
//! A program is a set of definite clauses `head ← body` over FOL terms
//! (atoms are terms: predicate = functor, 0-ary predicates are constants),
//! with a set of *abducible* predicate names and integrity constraints as
//! denials `← a₁,…,aₖ` (the body must not become derivable).
//!
//! The abductive proof procedure is SLD resolution with collection
//! (Kakas–Kowalski–Toni style, definite fragment): resolving a goal atom
//! whose predicate is abducible either reuses a hypothesis already in Δ or
//! adds the (instantiated) atom to Δ; other atoms resolve against program
//! clauses with fresh variable renaming. Completed derivations are kept only
//! if no denial body is derivable from program + Δ (abducibles then resolve
//! against Δ alone — the standard closed-world reading of hypotheses).
//!
//! Unification is Robinson-with-occurs-check on a trail, so the search
//! backtracks soundly. Answers are materialized Δ sets (dereferenced through
//! the final substitution); duplicates are eliminated set-semantically.
//!
//! This makes abduction genuinely first-order: hypotheses are instantiated
//! by unification (observe flies(tweety) → abduce normal(tweety)).

const std = @import("std");
const term_mod = @import("../fol/term.zig");

const TermPool = term_mod.TermPool;
const TermId = term_mod.TermId;

/// Error set of the recursive search (pool growth can hit interner limits).
const SearchError = error{ OutOfMemory, NoSpaceLeft };

pub const Clause = struct {
    head: TermId,
    body: []const TermId = &.{},
};

pub const Program = struct {
    clauses: []const Clause,
    /// Predicate (functor/constant) names whose atoms may be assumed.
    abducibles: []const []const u8,
    /// Denials: each body must never be jointly derivable from program + Δ.
    denials: []const []const TermId = &.{},
};

pub const Options = struct {
    max_solutions: u32 = 8,
    max_depth: u32 = 64,
    /// Global node budget across the whole search.
    max_steps: u64 = 100_000,
};

pub const Result = struct {
    allocator: std.mem.Allocator,
    /// Each solution: owned slice of materialized hypothesis atoms.
    solutions: std.ArrayList([]TermId) = .empty,
    /// Search space exhausted (no solution missed within depth/step budget).
    complete: bool = false,

    pub fn deinit(self: *Result) void {
        for (self.solutions.items) |s| self.allocator.free(s);
        self.solutions.deinit(self.allocator);
        self.* = undefined;
    }
};

// ── Trail-based unification ──────────────────────────────────────────

const Bindings = struct {
    allocator: std.mem.Allocator,
    map: std.AutoHashMapUnmanaged(u32, TermId) = .{},
    trail: std.ArrayList(u32) = .empty,

    fn deinit(self: *Bindings) void {
        self.map.deinit(self.allocator);
        self.trail.deinit(self.allocator);
    }

    fn mark(self: *const Bindings) usize {
        return self.trail.items.len;
    }

    fn undo(self: *Bindings, to: usize) void {
        while (self.trail.items.len > to) {
            const v = self.trail.pop().?;
            _ = self.map.remove(v);
        }
    }

    fn walk(self: *const Bindings, pool: *const TermPool, t: TermId) TermId {
        var cur = t;
        while (pool.isVar(cur)) {
            if (self.map.get(cur.index())) |n| cur = n else break;
        }
        return cur;
    }

    fn bind(self: *Bindings, v: TermId, t: TermId) !void {
        try self.map.put(self.allocator, v.index(), t);
        try self.trail.append(self.allocator, v.index());
    }
};

fn occurs(b: *const Bindings, pool: *const TermPool, v: TermId, t: TermId) bool {
    const w = b.walk(pool, t);
    if (w == v) return true;
    if (pool.tag(w) == .func) {
        for (pool.argsOf(w)) |a| {
            if (occurs(b, pool, v, a)) return true;
        }
    }
    return false;
}

fn unifyT(b: *Bindings, pool: *const TermPool, t1: TermId, t2: TermId) !bool {
    const a = b.walk(pool, t1);
    const c = b.walk(pool, t2);
    if (a == c) return true;
    if (pool.isVar(a)) {
        if (occurs(b, pool, a, c)) return false;
        try b.bind(a, c);
        return true;
    }
    if (pool.isVar(c)) {
        if (occurs(b, pool, c, a)) return false;
        try b.bind(c, a);
        return true;
    }
    if (pool.tag(a) != pool.tag(c)) return false;
    if (!std.mem.eql(u8, pool.nameOf(a), pool.nameOf(c))) return false;
    if (pool.tag(a) == .func) {
        const aa = pool.argsOf(a);
        const ca = pool.argsOf(c);
        if (aa.len != ca.len) return false;
        for (aa, ca) |x, y| {
            if (!try unifyT(b, pool, x, y)) return false;
        }
    }
    return true;
}

/// Rebuild a term with all bound variables dereferenced.
fn materialize(b: *const Bindings, pool: *TermPool, t: TermId) !TermId {
    const w = b.walk(pool, t);
    if (pool.tag(w) != .func) return w;
    const args = pool.argsOf(w);
    var new_args = try pool.allocator.alloc(TermId, args.len);
    defer pool.allocator.free(new_args);
    var changed = false;
    for (args, 0..) |a, i| {
        new_args[i] = try materialize(b, pool, a);
        if (new_args[i] != a) changed = true;
    }
    if (!changed) return w;
    return pool.mkFunc(pool.nameOf(w), new_args);
}

/// Fresh-variable renaming of a term (per clause use).
fn rename(
    pool: *TermPool,
    var_map: *std.AutoHashMapUnmanaged(u32, TermId),
    allocator: std.mem.Allocator,
    t: TermId,
) !TermId {
    switch (pool.tag(t)) {
        .variable => {
            if (var_map.get(t.index())) |v| return v;
            const fresh = try pool.mkVar(pool.rawNameOf(t));
            try var_map.put(allocator, t.index(), fresh);
            return fresh;
        },
        .constant => return t,
        .func => {
            const args = pool.argsOf(t);
            var new_args = try allocator.alloc(TermId, args.len);
            defer allocator.free(new_args);
            for (args, 0..) |a, i| new_args[i] = try rename(pool, var_map, allocator, a);
            return pool.mkFunc(pool.nameOf(t), new_args);
        },
    }
}

fn predName(pool: *const TermPool, t: TermId) []const u8 {
    return pool.nameOf(t);
}

fn isAbducible(program: *const Program, pool: *const TermPool, t: TermId) bool {
    const name = predName(pool, t);
    for (program.abducibles) |a| {
        if (std.mem.eql(u8, a, name)) return true;
    }
    return false;
}

// ── Search state ─────────────────────────────────────────────────────

const Search = struct {
    allocator: std.mem.Allocator,
    pool: *TermPool,
    program: *const Program,
    opts: Options,
    bindings: Bindings,
    delta: std.ArrayList(TermId) = .empty,
    steps: u64 = 0,
    truncated: bool = false,
    result: *Result,
    seen: std.StringHashMapUnmanaged(void) = .{},

    fn deinit(self: *Search) void {
        self.bindings.deinit();
        self.delta.deinit(self.allocator);
        var it = self.seen.keyIterator();
        while (it.next()) |k| self.allocator.free(k.*);
        self.seen.deinit(self.allocator);
    }

    fn budget(self: *Search, depth: u32) bool {
        self.steps += 1;
        if (self.steps > self.opts.max_steps or depth > self.opts.max_depth) {
            self.truncated = true;
            return false;
        }
        return true;
    }

    fn printTerm(self: *Search, out: *std.ArrayList(u8), t: TermId) !void {
        const w = self.bindings.walk(self.pool, t);
        try out.appendSlice(self.allocator, self.pool.nameOf(w));
        if (self.pool.tag(w) == .func) {
            try out.append(self.allocator, '(');
            for (self.pool.argsOf(w), 0..) |a, i| {
                if (i > 0) try out.append(self.allocator, ',');
                try self.printTerm(out, a);
            }
            try out.append(self.allocator, ')');
        } else if (self.pool.isVar(w)) {
            try out.append(self.allocator, '#');
            var buf: [12]u8 = undefined;
            const s = std.fmt.bufPrint(&buf, "{d}", .{w.index()}) catch unreachable;
            try out.appendSlice(self.allocator, s);
        }
    }

    /// Record the current Δ as a solution (dedup by canonical print).
    fn record(self: *Search) !void {
        // Denial check: no integrity-constraint body may be derivable.
        for (self.program.denials) |denial| {
            if (try self.derivableAll(denial, 0)) return;
        }
        var atoms = try self.allocator.alloc(TermId, self.delta.items.len);
        errdefer self.allocator.free(atoms);
        for (self.delta.items, 0..) |d, i| atoms[i] = try materialize(&self.bindings, self.pool, d);
        std.mem.sort(TermId, atoms, {}, struct {
            fn less(_: void, x: TermId, y: TermId) bool {
                return x.index() < y.index();
            }
        }.less);
        // Set semantics: drop duplicate atoms.
        var n: usize = 0;
        for (atoms) |a| {
            if (n == 0 or atoms[n - 1] != a) {
                atoms[n] = a;
                n += 1;
            }
        }
        var key: std.ArrayList(u8) = .empty;
        defer key.deinit(self.allocator);
        for (atoms[0..n]) |a| {
            try self.printTerm(&key, a);
            try key.append(self.allocator, ';');
        }
        if (self.seen.contains(key.items)) {
            self.allocator.free(atoms);
            return;
        }
        try self.seen.put(self.allocator, try self.allocator.dupe(u8, key.items), {});
        const owned = try self.allocator.realloc(atoms, n);
        try self.result.solutions.append(self.allocator, owned);
    }

    /// Abductive SLD search. `goals` is an immutable snapshot; resolution
    /// builds a fresh list (renamed body ++ remaining goals), so continuations
    /// are correct at any nesting depth.
    fn solveG(self: *Search, goals: []const TermId, depth: u32) SearchError!void {
        if (self.result.solutions.items.len >= self.opts.max_solutions) return;
        if (!self.budget(depth)) return;
        if (goals.len == 0) {
            try self.record();
            return;
        }
        const g = goals[0];

        if (isAbducible(self.program, self.pool, self.bindings.walk(self.pool, g))) {
            // Reuse an existing hypothesis.
            for (0..self.delta.items.len) |di| {
                const mrk = self.bindings.mark();
                if (try unifyT(&self.bindings, self.pool, g, self.delta.items[di])) {
                    try self.solveG(goals[1..], depth + 1);
                }
                self.bindings.undo(mrk);
            }
            // Assume it afresh.
            try self.delta.append(self.allocator, g);
            try self.solveG(goals[1..], depth + 1);
            _ = self.delta.pop();
            return;
        }
        // Resolve against program clauses (body first, depth-first).
        for (self.program.clauses) |cl| {
            const mrk = self.bindings.mark();
            var var_map: std.AutoHashMapUnmanaged(u32, TermId) = .{};
            defer var_map.deinit(self.allocator);
            const head = try rename(self.pool, &var_map, self.allocator, cl.head);
            if (try unifyT(&self.bindings, self.pool, g, head)) {
                const next = try self.allocator.alloc(TermId, cl.body.len + goals.len - 1);
                defer self.allocator.free(next);
                for (cl.body, 0..) |bd, i| {
                    next[i] = try rename(self.pool, &var_map, self.allocator, bd);
                }
                @memcpy(next[cl.body.len..], goals[1..]);
                try self.solveG(next, depth + 1);
            }
            self.bindings.undo(mrk);
        }
    }

    /// Deductive check: are all `atoms` derivable from program + Δ-as-facts?
    /// Abducible atoms resolve only against Δ here.
    fn derivableAll(self: *Search, atoms: []const TermId, depth: u32) SearchError!bool {
        var found = false;
        try self.derive(atoms, 0, depth, &found);
        return found;
    }

    fn derive(self: *Search, atoms: []const TermId, i: usize, depth: u32, found: *bool) SearchError!void {
        if (found.*) return;
        if (depth > self.opts.max_depth) {
            self.truncated = true;
            return;
        }
        if (i >= atoms.len) {
            found.* = true;
            return;
        }
        const g = atoms[i];
        if (isAbducible(self.program, self.pool, self.bindings.walk(self.pool, g))) {
            for (self.delta.items) |d| {
                const mrk = self.bindings.mark();
                if (try unifyT(&self.bindings, self.pool, g, d)) {
                    try self.derive(atoms, i + 1, depth + 1, found);
                }
                self.bindings.undo(mrk);
                if (found.*) return;
            }
            return;
        }
        for (self.program.clauses) |cl| {
            const mrk = self.bindings.mark();
            var var_map: std.AutoHashMapUnmanaged(u32, TermId) = .{};
            defer var_map.deinit(self.allocator);
            const head = try rename(self.pool, &var_map, self.allocator, cl.head);
            if (try unifyT(&self.bindings, self.pool, g, head)) {
                if (cl.body.len == 0) {
                    try self.derive(atoms, i + 1, depth + 1, found);
                } else {
                    var ext: std.ArrayList(TermId) = .empty;
                    defer ext.deinit(self.allocator);
                    for (cl.body) |bd| try ext.append(self.allocator, try rename(self.pool, &var_map, self.allocator, bd));
                    for (atoms[i + 1 ..]) |rest| try ext.append(self.allocator, rest);
                    try self.derive(ext.items, 0, depth + 1, found);
                }
            }
            self.bindings.undo(mrk);
            if (found.*) return;
        }
    }
};

/// Abduce hypothesis sets Δ of abducible atoms such that program + Δ derives
/// every goal atom and no denial fires.
pub fn abduce(
    allocator: std.mem.Allocator,
    pool: *TermPool,
    program: Program,
    goal: []const TermId,
    opts: Options,
) !Result {
    var result = Result{ .allocator = allocator };
    errdefer result.deinit();
    var s = Search{
        .allocator = allocator,
        .pool = pool,
        .program = &program,
        .opts = opts,
        .bindings = .{ .allocator = allocator },
        .result = &result,
    };
    defer s.deinit();
    try s.solveG(goal, 0);
    result.complete = !s.truncated and result.solutions.items.len < opts.max_solutions;
    return result;
}

/// Independent deductive re-check: program + Δ ⊢ every goal atom.
pub fn derives(
    allocator: std.mem.Allocator,
    pool: *TermPool,
    program: Program,
    delta: []const TermId,
    goal: []const TermId,
    opts: Options,
) !bool {
    var result = Result{ .allocator = allocator };
    defer result.deinit();
    var s = Search{
        .allocator = allocator,
        .pool = pool,
        .program = &program,
        .opts = opts,
        .bindings = .{ .allocator = allocator },
        .result = &result,
    };
    defer s.deinit();
    try s.delta.appendSlice(allocator, delta);
    return s.derivableAll(goal, 0);
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

fn atomStr(allocator: std.mem.Allocator, pool: *const TermPool, t: TermId) ![]u8 {
    var out: std.ArrayList(u8) = .empty;
    errdefer out.deinit(allocator);
    try out.appendSlice(allocator, pool.nameOf(t));
    if (pool.tag(t) == .func) {
        try out.append(allocator, '(');
        for (pool.argsOf(t), 0..) |a, i| {
            if (i > 0) try out.append(allocator, ',');
            const s = try atomStr(allocator, pool, a);
            defer allocator.free(s);
            try out.appendSlice(allocator, s);
        }
        try out.append(allocator, ')');
    }
    return out.toOwnedSlice(allocator);
}

fn expectSolutionAtoms(pool: *const TermPool, sol: []const TermId, expected: []const []const u8) !void {
    try testing.expectEqual(expected.len, sol.len);
    for (sol, expected) |a, e| {
        const s = try atomStr(testing.allocator, pool, a);
        defer testing.allocator.free(s);
        try testing.expectEqualStrings(e, s);
    }
}

test "alp: grass-wet — two rival hypotheses, denial kills one" {
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const wet = try pool.mkConst("wet");
    const rained = try pool.mkConst("rained");
    const sprinkler = try pool.mkConst("sprinkler");
    const clauses = [_]Clause{
        .{ .head = wet, .body = &.{rained} },
        .{ .head = wet, .body = &.{sprinkler} },
    };
    const abd = [_][]const u8{ "rained", "sprinkler" };
    {
        var r = try abduce(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{wet}, .{});
        defer r.deinit();
        try testing.expect(r.complete);
        try testing.expectEqual(@as(usize, 2), r.solutions.items.len);
        for (r.solutions.items) |sol| {
            try testing.expectEqual(@as(usize, 1), sol.len);
            try testing.expect(try derives(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, sol, &.{wet}, .{}));
        }
    }
    {
        // Integrity: it did not rain.
        const denials = [_][]const TermId{&.{rained}};
        var r = try abduce(testing.allocator, &pool, .{
            .clauses = &clauses,
            .abducibles = &abd,
            .denials = &denials,
        }, &.{wet}, .{});
        defer r.deinit();
        try testing.expectEqual(@as(usize, 1), r.solutions.items.len);
        try expectSolutionAtoms(&pool, r.solutions.items[0], &.{"sprinkler"});
    }
}

test "alp: first-order instantiation — abduce normal(tweety)" {
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const tweety = try pool.mkConst("tweety");
    const x = try pool.mkVar("X");
    const bird_t = try pool.mkFunc("bird", &.{tweety});
    const bird_x = try pool.mkFunc("bird", &.{x});
    const normal_x = try pool.mkFunc("normal", &.{x});
    const flies_x = try pool.mkFunc("flies", &.{x});
    const flies_t = try pool.mkFunc("flies", &.{tweety});
    const clauses = [_]Clause{
        .{ .head = bird_t },
        .{ .head = flies_x, .body = &.{ bird_x, normal_x } },
    };
    const abd = [_][]const u8{"normal"};
    var r = try abduce(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{flies_t}, .{});
    defer r.deinit();
    try testing.expect(r.complete);
    try testing.expectEqual(@as(usize, 1), r.solutions.items.len);
    try expectSolutionAtoms(&pool, r.solutions.items[0], &.{"normal(tweety)"});
}

test "alp: denial with variables — penguins are never normal" {
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const tweety = try pool.mkConst("tweety");
    const x = try pool.mkVar("X");
    const y = try pool.mkVar("Y");
    const clauses = [_]Clause{
        .{ .head = try pool.mkFunc("bird", &.{tweety}) },
        .{ .head = try pool.mkFunc("penguin", &.{tweety}) },
        .{ .head = try pool.mkFunc("flies", &.{x}), .body = &.{
            try pool.mkFunc("bird", &.{x}),
            try pool.mkFunc("normal", &.{x}),
        } },
    };
    const abd = [_][]const u8{"normal"};
    const denials = [_][]const TermId{&.{
        try pool.mkFunc("normal", &.{y}),
        try pool.mkFunc("penguin", &.{y}),
    }};
    var r = try abduce(testing.allocator, &pool, .{
        .clauses = &clauses,
        .abducibles = &abd,
        .denials = &denials,
    }, &.{try pool.mkFunc("flies", &.{tweety})}, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 0), r.solutions.items.len);
}

test "alp: goal derivable without hypotheses → empty delta" {
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const tweety = try pool.mkConst("tweety");
    const bird_t = try pool.mkFunc("bird", &.{tweety});
    const clauses = [_]Clause{.{ .head = bird_t }};
    const abd = [_][]const u8{"normal"};
    var r = try abduce(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{bird_t}, .{});
    defer r.deinit();
    try testing.expectEqual(@as(usize, 1), r.solutions.items.len);
    try testing.expectEqual(@as(usize, 0), r.solutions.items[0].len);
}

test "alp: shared hypothesis reused across subgoals (set semantics)" {
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const a = try pool.mkConst("a");
    const p = try pool.mkConst("p");
    const q = try pool.mkConst("q");
    const clauses = [_]Clause{
        .{ .head = p, .body = &.{a} },
        .{ .head = q, .body = &.{a} },
    };
    const abd = [_][]const u8{"a"};
    var r = try abduce(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{ p, q }, .{});
    defer r.deinit();
    try testing.expect(r.solutions.items.len >= 1);
    // Every solution is exactly {a} after set-dedup.
    for (r.solutions.items) |sol| {
        try expectSolutionAtoms(&pool, sol, &.{"a"});
    }
    try testing.expectEqual(@as(usize, 1), r.solutions.items.len);
}

test "alp: chained rules with function terms" {
    // path(X,Z) ← edge(X,Z); path(X,Z) ← edge(X,Y), path(Y,Z); edges abducible.
    var pool = TermPool.init(testing.allocator);
    defer pool.deinit();
    const n1 = try pool.mkConst("n1");
    const n3 = try pool.mkConst("n3");
    const x = try pool.mkVar("X");
    const y = try pool.mkVar("Y");
    const z = try pool.mkVar("Z");
    const clauses = [_]Clause{
        .{ .head = try pool.mkFunc("path", &.{ x, z }), .body = &.{try pool.mkFunc("edge", &.{ x, z })} },
        .{ .head = try pool.mkFunc("path", &.{ x, z }), .body = &.{
            try pool.mkFunc("edge", &.{ x, y }),
            try pool.mkFunc("path", &.{ y, z }),
        } },
    };
    const abd = [_][]const u8{"edge"};
    var r = try abduce(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{
        try pool.mkFunc("path", &.{ n1, n3 }),
    }, .{ .max_depth = 8, .max_solutions = 3 });
    defer r.deinit();
    try testing.expect(r.solutions.items.len >= 1);
    // First (shallowest) solution: a single direct edge n1→n3.
    try expectSolutionAtoms(&pool, r.solutions.items[0], &.{"edge(n1,n3)"});
    // Deductive re-check of every returned hypothesis set.
    for (r.solutions.items) |sol| {
        try testing.expect(try derives(testing.allocator, &pool, .{ .clauses = &clauses, .abducibles = &abd }, sol, &.{
            try pool.mkFunc("path", &.{ n1, n3 }),
        }, .{ .max_depth = 8 }));
    }
}
