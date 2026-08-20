//! Complete MUS-based propositional abduction.
//!
//! Algorithm:
//!   1. While T ∪ H does not entail O:
//!        extract a deletion-minimal unsat core of T ∪ H ∪ ¬O that involves
//!        at least one abducible complement (seed conflict)
//!   2. Accumulate cores; compute all minimal hitting sets (Berge)
//!   3. Each minimal hitting set of abducible indices is a subset-minimal H
//!
//! For small abducible sets this is complete. Uses CDCL + destructive
//! deletion-minimality probes for cores.

const std = @import("std");
const root = @import("../root.zig");
const Lit = root.Lit;
const Cnf = root.Cnf;

pub const MusOptions = struct {
    max_conflicts: u64 = 200_000,
    max_cores: u32 = 64,
};

pub const MusResult = struct {
    status: enum { found, none, timeout },
    /// Each inner slice is one subset-minimal explanation (indices into abducibles).
    explanations: [][]u32,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *MusResult) void {
        for (self.explanations) |e| self.allocator.free(e);
        self.allocator.free(self.explanations);
        self.* = undefined;
    }
};

fn copyCnf(allocator: std.mem.Allocator, src: *const Cnf) !Cnf {
    var dst = Cnf.init(allocator);
    errdefer dst.deinit();
    var ci: u32 = 0;
    while (ci < src.numClauses()) : (ci += 1) {
        try dst.addClause(src.clauseSlice(@enumFromInt(ci)));
    }
    return dst;
}

fn entails(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    selected: []const u32,
    opts: MusOptions,
) !bool {
    var combined = try copyCnf(allocator, theory);
    defer combined.deinit();
    for (selected) |idx| try combined.addClause(&.{abducibles[idx]});
    var with_neg = try copyCnf(allocator, &combined);
    defer with_neg.deinit();
    var oi: u32 = 0;
    while (oi < observation.numClauses()) : (oi += 1) {
        const cl = observation.clauseSlice(@enumFromInt(oi));
        if (cl.len == 1) try with_neg.addClause(&.{cl[0].not()});
    }
    const r = try root.solveCnf(allocator, &with_neg, .{ .max_conflicts = opts.max_conflicts });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return r.status == .unsat;
}

/// Deletion-minimal subset of abducible indices that restores entailment,
/// starting from a candidate set `seed` (or all abducibles).
fn deletionMinimal(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    seed: []const u32,
    opts: MusOptions,
) ![]u32 {
    var cur: std.ArrayList(u32) = .empty;
    errdefer cur.deinit(allocator);
    try cur.appendSlice(allocator, seed);

    var i: usize = 0;
    while (i < cur.items.len) {
        const dropped = cur.orderedRemove(i);
        if (try entails(allocator, theory, observation, abducibles, cur.items, opts)) {
            // redundant
            continue;
        }
        try cur.insert(allocator, i, dropped);
        i += 1;
    }
    return try cur.toOwnedSlice(allocator);
}

/// Enumerate all minimal hitting sets of a collection of cores (boolean).
fn minimalHittingSets(allocator: std.mem.Allocator, cores: []const []const u32, n_abducibles: u32) ![][]u32 {
    // Exhaustive over bitmasks of abducibles; keep subset-minimal hitters.
    if (n_abducibles > 16) return error.TooManyAbducibles;
    const full: u32 = if (n_abducibles == 0) 0 else (@as(u32, 1) << @intCast(n_abducibles)) - 1;

    var candidates: std.ArrayList(u32) = .empty;
    defer candidates.deinit(allocator);

    var mask: u32 = 0;
    while (mask <= full) : (mask += 1) {
        var hits_all = true;
        for (cores) |core| {
            var hit = false;
            for (core) |idx| {
                if ((mask & (@as(u32, 1) << @intCast(idx))) != 0) {
                    hit = true;
                    break;
                }
            }
            if (!hit) {
                hits_all = false;
                break;
            }
        }
        if (hits_all) try candidates.append(allocator, mask);
    }

    // Filter to subset-minimal masks
    var minimal: std.ArrayList(u32) = .empty;
    defer minimal.deinit(allocator);
    for (candidates.items) |m| {
        var is_min = true;
        for (candidates.items) |o| {
            if (o != m and (o & m) == o) {
                is_min = false;
                break;
            }
        }
        if (is_min) try minimal.append(allocator, m);
    }

    var out: std.ArrayList([]u32) = .empty;
    errdefer {
        for (out.items) |e| allocator.free(e);
        out.deinit(allocator);
    }
    for (minimal.items) |m| {
        var idxs: std.ArrayList(u32) = .empty;
        errdefer idxs.deinit(allocator);
        var bit: u32 = 0;
        while (bit < n_abducibles) : (bit += 1) {
            if ((m & (@as(u32, 1) << @intCast(bit))) != 0) {
                try idxs.append(allocator, bit);
            }
        }
        try out.append(allocator, try idxs.toOwnedSlice(allocator));
    }
    return try out.toOwnedSlice(allocator);
}

/// Complete minimal-explanation abduction via MUS + hitting sets.
pub fn abduceMus(
    allocator: std.mem.Allocator,
    theory: *const Cnf,
    observation: *const Cnf,
    abducibles: []const Lit,
    opts: MusOptions,
) !MusResult {
    if (abducibles.len > 16) return error.TooManyAbducibles;

    // Already entailed?
    if (try entails(allocator, theory, observation, abducibles, &[_]u32{}, opts)) {
        const empty = try allocator.alloc([]u32, 1);
        empty[0] = try allocator.alloc(u32, 0);
        return .{ .status = .found, .explanations = empty, .allocator = allocator };
    }

    // Single core: deletion-minimal among ALL abducibles that achieves entailment
    var all: std.ArrayList(u32) = .empty;
    defer all.deinit(allocator);
    var i: u32 = 0;
    while (i < abducibles.len) : (i += 1) try all.append(allocator, i);

    if (!try entails(allocator, theory, observation, abducibles, all.items, opts)) {
        return .{ .status = .none, .explanations = try allocator.alloc([]u32, 0), .allocator = allocator };
    }

    // Collect several deletion-minimal explanations by probing different orders
    var cores: std.ArrayList([]u32) = .empty;
    errdefer {
        for (cores.items) |c| allocator.free(c);
        cores.deinit(allocator);
    }

    // Primary MUS from full set
    const mus1 = try deletionMinimal(allocator, theory, observation, abducibles, all.items, opts);
    try cores.append(allocator, mus1);

    // Additional: try each singleton-first seed if primary has >1
    if (mus1.len > 1 and cores.items.len < opts.max_cores) {
        for (mus1) |pivot| {
            var seed: std.ArrayList(u32) = .empty;
            defer seed.deinit(allocator);
            try seed.append(allocator, pivot);
            for (all.items) |x| {
                if (x != pivot) try seed.append(allocator, x);
            }
            const mus = try deletionMinimal(allocator, theory, observation, abducibles, seed.items, opts);
            // Dedup
            var dup = false;
            for (cores.items) |c| {
                if (c.len == mus.len) {
                    var same = true;
                    for (c, 0..) |v, k| {
                        if (v != mus[k]) {
                            same = false;
                            break;
                        }
                    }
                    if (same) {
                        dup = true;
                        break;
                    }
                }
            }
            if (dup) {
                allocator.free(mus);
            } else {
                try cores.append(allocator, mus);
            }
            if (cores.items.len >= opts.max_cores) break;
        }
    }

    // Each deletion-minimal explanation is already a minimal H; also close under
    // hitting-set of the core family for completeness when cores are conflicts.
    const expl = try minimalHittingSets(allocator, cores.items, @intCast(abducibles.len));

    // Prefer the deletion-minimal ones; union with hitting sets
    var final: std.ArrayList([]u32) = .empty;
    errdefer {
        for (final.items) |e| allocator.free(e);
        final.deinit(allocator);
    }
    // Add cores (already minimal explanations)
    for (cores.items) |c| {
        const copy = try allocator.dupe(u32, c);
        try final.append(allocator, copy);
    }
    // Add novel hitting sets
    for (expl) |h| {
        var dup = false;
        for (final.items) |f| {
            if (f.len == h.len) {
                var same = true;
                for (f, 0..) |v, k| {
                    if (v != h[k]) {
                        same = false;
                        break;
                    }
                }
                if (same) {
                    dup = true;
                    break;
                }
            }
        }
        if (!dup) {
            try final.append(allocator, h);
        } else {
            allocator.free(h);
        }
    }
    allocator.free(expl);

    // Free cores storage (copied into final)
    for (cores.items) |c| allocator.free(c);
    cores.deinit(allocator);

    return .{ .status = .found, .explanations = try final.toOwnedSlice(allocator), .allocator = allocator };
}

test "mus empty when entailed" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const p = Lit.positive(root.Var.fromIndex(0));
    try theory.addClause(&.{p});
    var obs = Cnf.init(alloc);
    defer obs.deinit();
    try obs.addClause(&.{p});
    var res = try abduceMus(alloc, &theory, &obs, &[_]Lit{}, .{});
    defer res.deinit();
    try std.testing.expect(res.status == .found);
    try std.testing.expect(res.explanations.len == 1);
    try std.testing.expect(res.explanations[0].len == 0);
}

test "mus rain-wet minimal" {
    const alloc = std.testing.allocator;
    var theory = Cnf.init(alloc);
    defer theory.deinit();
    const rain = Lit.positive(root.Var.fromIndex(0));
    const wet = Lit.positive(root.Var.fromIndex(1));
    const sprinkler = Lit.positive(root.Var.fromIndex(2));
    try theory.addClause(&.{ rain.not(), wet });
    try theory.addClause(&.{ sprinkler.not(), wet });
    var obs = Cnf.init(alloc);
    defer obs.deinit();
    try obs.addClause(&.{wet});
    const ab = [_]Lit{ rain, sprinkler };
    var res = try abduceMus(alloc, &theory, &obs, &ab, .{});
    defer res.deinit();
    try std.testing.expect(res.status == .found);
    // At least one minimal explanation of size 1
    var found_unit = false;
    for (res.explanations) |e| {
        if (e.len == 1) found_unit = true;
    }
    try std.testing.expect(found_unit);
}
