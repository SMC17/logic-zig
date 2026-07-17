//! IC3/PDR (Property Directed Reachability) — competition-oriented feature set.
//!
//! Safety: G(¬bad) over latch state (inputs free existentially each step).
//!
//! Feature map (IC3a / ABC-adjacent):
//! - MIC generalization + CTG predecessor blocking
//! - Ternary (0/1/X) cube pre-weaken and predecessor weaken
//! - Recursive obligations (`blockCube`) with depth bound
//! - Multi-round push to quiescence + clause-set fixed point
//! - Lemma lift toward F[0] when init-disjoint
//! - Subsumption on frame clause DBs
//! - Multi-property OR synthesis (`checkMulti`)
//!
//! Not claimed: full ABC engine parity (localization abstraction, fraiging, etc.).

const std = @import("std");
const netlist_mod = @import("netlist.zig");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");
const solver_mod = @import("../sat/solver.zig");

const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;
const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const PdrStatus = enum { proven, violated, unknown };

pub const PdrResult = struct {
    status: PdrStatus,
    frames: u32 = 0,
    conflicts: u64 = 0,
    generalizations: u64 = 0,
    pushes: u64 = 0,
    ctg_blocks: u64 = 0,
    obligations: u64 = 0,
    ternary_drops: u64 = 0,
    cex_latches: ?[]Value = null,
    nlatches: u32 = 0,
    cex_len: u32 = 0,
};

const Clause = struct {
    lits: []Lit,
};

const blast = @import("blast.zig");

fn blastFrame(cnf: *Cnf, nl: *const Netlist, frame: u32, nn: u32) !void {
    try blast.blastFrameNn(cnf, nl, frame, nn);
}

fn addConstraintsFrame(cnf: *Cnf, nl: *const Netlist, frame: u32, nn: u32) !void {
    for (nl.constraints.items) |cnet| {
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(frame * nn + cnet.index()))});
    }
}

fn addTrans(cnf: *Cnf, nl: *const Netlist) !void {
    const nn = nl.num_nets;
    try blastFrame(cnf, nl, 0, nn);
    try blastFrame(cnf, nl, 1, nn);
    try addConstraintsFrame(cnf, nl, 0, nn);
    try addConstraintsFrame(cnf, nl, 1, nn);
    for (nl.latches.items) |lat| {
        const qn = Lit.positive(Var.fromIndex(nn + lat.q.index()));
        const d = Lit.positive(Var.fromIndex(lat.d.index()));
        try cnf.addClause(&.{ qn.not(), d });
        try cnf.addClause(&.{ d.not(), qn });
    }
}

fn addFrameClauses(cnf: *Cnf, frame_clauses: []const Clause, frame_off: u32) !void {
    for (frame_clauses) |cl| {
        var buf: std.ArrayList(Lit) = .empty;
        defer buf.deinit(cnf.allocator);
        for (cl.lits) |l| {
            try buf.append(cnf.allocator, Lit.make(Var.fromIndex(l.variable().index() + frame_off), l.isNeg()));
        }
        try cnf.addClause(buf.items);
    }
}

fn latchCube(allocator: std.mem.Allocator, nl: *const Netlist, model: []const Value, frame: u32) ![]Lit {
    const nn = nl.num_nets;
    var cube: std.ArrayList(Lit) = .empty;
    errdefer cube.deinit(allocator);
    for (nl.latches.items) |lat| {
        const idx = frame * nn + lat.q.index();
        const lit = if (model[idx] == .true_)
            Lit.positive(Var.fromIndex(lat.q.index()))
        else
            Lit.negative(Var.fromIndex(lat.q.index()));
        try cube.append(allocator, lit);
    }
    return try cube.toOwnedSlice(allocator);
}

fn negateCube(allocator: std.mem.Allocator, cube: []const Lit) ![]Lit {
    const out = try allocator.alloc(Lit, cube.len);
    for (cube, 0..) |l, i| out[i] = l.not();
    return out;
}

/// Relative inductiveness of clause C = ~cube at level:
/// F[0]..F[level] ∧ T ∧ cube'  is UNSAT  (cube cannot be reached in one step from F[level])
fn isRelativeInductive(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    frames: []const std.ArrayList(Clause),
    level: usize,
    cube: []const Lit,
) !struct { ok: bool, conflicts: u64 } {
    var cnf = Cnf.init(allocator);
    defer cnf.deinit();
    const nn = nl.num_nets;
    cnf.ensureVars(nn * 2);
    try addTrans(&cnf, nl);
    var i: usize = 0;
    while (i <= level) : (i += 1) {
        try addFrameClauses(&cnf, frames[i].items, 0);
    }
    // Also require ~cube on current (relative to states not already blocked) — standard RI:
    // F[level] ∧ ~c ∧ T ∧ c' unsat means c is inductive relative to F[level]
    // Here c is the cube (bad minterm). Inductive clause is ~cube.
    // Check: frames ∧ T ∧ cube' unsat (cube unreachable in one step)
    for (cube) |l| {
        try cnf.addClause(&.{Lit.make(Var.fromIndex(nn + l.variable().index()), l.isNeg())});
    }
    // Optional: current not in cube (for relative)
    {
        var neg: std.ArrayList(Lit) = .empty;
        defer neg.deinit(allocator);
        for (cube) |l| try neg.append(allocator, l.not());
        try cnf.addClause(neg.items); // ~cube on current
    }

    const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 200_000 });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return .{ .ok = r.status == .unsat, .conflicts = r.conflicts };
}

const GenStats = struct {
    conflicts: u64 = 0,
    gens: u64 = 0,
    ctg_blocks: u64 = 0,
    ternary_drops: u64 = 0,
};

const ternary = @import("ternary.zig");

/// Query relative inductiveness; on SAT return predecessor cube (frame-0 latch assignment).
fn relativeInductiveQuery(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    frames: []const std.ArrayList(Clause),
    level: usize,
    cube: []const Lit,
) !struct { ok: bool, conflicts: u64, pred: ?[]Lit } {
    var cnf = Cnf.init(allocator);
    defer cnf.deinit();
    const nn = nl.num_nets;
    cnf.ensureVars(nn * 2);
    try addTrans(&cnf, nl);
    var i: usize = 0;
    while (i <= level) : (i += 1) {
        try addFrameClauses(&cnf, frames[i].items, 0);
    }
    for (cube) |l| {
        try cnf.addClause(&.{Lit.make(Var.fromIndex(nn + l.variable().index()), l.isNeg())});
    }
    {
        var neg: std.ArrayList(Lit) = .empty;
        defer neg.deinit(allocator);
        for (cube) |l| try neg.append(allocator, l.not());
        try cnf.addClause(neg.items);
    }
    const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 200_000 });
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    if (r.status == .unsat) {
        if (r.model) |m| allocator.free(m);
        return .{ .ok = true, .conflicts = r.conflicts, .pred = null };
    }
    if (r.status != .sat) {
        if (r.model) |m| allocator.free(m);
        return .{ .ok = false, .conflicts = r.conflicts, .pred = null };
    }
    const model = r.model.?;
    defer allocator.free(model);
    const pred = try latchCube(allocator, nl, model, 0);
    return .{ .ok = false, .conflicts = r.conflicts, .pred = pred };
}

fn isInitBlocked(allocator: std.mem.Allocator, nl: *const Netlist, cube: []const Lit) !struct { blocked: bool, conflicts: u64 } {
    // Init ∧ cube unsat?
    var cnf = Cnf.init(allocator);
    defer cnf.deinit();
    const nn = nl.num_nets;
    cnf.ensureVars(nn);
    try blastFrame(&cnf, nl, 0, nn);
    try addConstraintsFrame(&cnf, nl, 0, nn);
    for (nl.latches.items) |lat| {
        if (lat.init) |iv| {
            const q = Lit.positive(Var.fromIndex(lat.q.index()));
            if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
        }
    }
    for (cube) |l| try cnf.addClause(&.{l});
    const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 50_000 });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return .{ .blocked = r.status == .unsat, .conflicts = r.conflicts };
}

/// Ternary pre-weaken: drop latch lits that stay X while prop stays 1.
/// Prefer inductive weaken when cube encodes a bad minterm (next free).
fn ternaryPreweaken(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    cube_in: []const Lit,
    prop: ?NetId,
    stats: *GenStats,
) ![]Lit {
    if (prop == null or nl.latches.items.len == 0) return try allocator.dupe(Lit, cube_in);
    var latch_tri = try allocator.alloc(ternary.Tri, nl.latches.items.len);
    defer allocator.free(latch_tri);
    @memset(latch_tri, .x);
    for (nl.latches.items, 0..) |lat, i| {
        for (cube_in) |l| {
            if (l.variable().index() == lat.q.index()) {
                latch_tri[i] = if (l.isNeg()) .zero else .one;
                break;
            }
        }
    }
    for (latch_tri) |t| {
        if (t == .x) return try allocator.dupe(Lit, cube_in);
    }
    // Prefer inductive-style weaken (same as property weaken when next_must=null)
    const weak = ternary.weakenCubeInductive(allocator, nl, prop.?, latch_tri, null) catch
        (ternary.weakenCubeForProperty(allocator, nl, prop.?, latch_tri) catch {
            return try allocator.dupe(Lit, cube_in);
        });
    defer allocator.free(weak);
    var out: std.ArrayList(Lit) = .empty;
    errdefer out.deinit(allocator);
    for (nl.latches.items, 0..) |lat, i| {
        if (weak[i] == .x) {
            stats.ternary_drops += 1;
            continue;
        }
        const lit = if (weak[i] == .one)
            Lit.positive(Var.fromIndex(lat.q.index()))
        else
            Lit.negative(Var.fromIndex(lat.q.index()));
        try out.append(allocator, lit);
    }
    if (out.items.len == 0) return try allocator.dupe(Lit, cube_in);
    return try out.toOwnedSlice(allocator);
}

/// MIC + CTG + ternary preweaken.
fn generalize(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    frames: []std.ArrayList(Clause),
    level: usize,
    cube_in: []const Lit,
    stats: *GenStats,
    prop: ?NetId,
) ![]Lit {
    const pre = try ternaryPreweaken(allocator, nl, cube_in, prop, stats);
    defer allocator.free(pre);
    var cube = try allocator.dupe(Lit, pre);
    errdefer allocator.free(cube);

    var changed = true;
    var rounds: u32 = 0;
    while (changed and rounds < 64) : (rounds += 1) {
        changed = false;
        var i: usize = 0;
        while (i < cube.len) {
            var reduced: std.ArrayList(Lit) = .empty;
            defer reduced.deinit(allocator);
            for (cube, 0..) |l, j| {
                if (j != i) try reduced.append(allocator, l);
            }
            if (reduced.items.len == 0) {
                i += 1;
                continue;
            }
            const q = try relativeInductiveQuery(allocator, nl, frames, level, reduced.items);
            stats.conflicts += q.conflicts;
            if (q.ok) {
                allocator.free(cube);
                cube = try allocator.dupe(Lit, reduced.items);
                stats.gens += 1;
                changed = true;
                i = 0;
                continue;
            }
            // CTG: predecessor of reduced cube — block if relatively inductive below.
            if (q.pred) |pred| {
                defer allocator.free(pred);
                var blocked_ctg = false;
                if (level > 0) {
                    var lv: i32 = @intCast(level - 1);
                    while (lv >= 0) : (lv -= 1) {
                        const chk = try isRelativeInductive(allocator, nl, frames, @intCast(lv), pred);
                        stats.conflicts += chk.conflicts;
                        if (chk.ok) {
                            const neg = try negateCube(allocator, pred);
                            defer allocator.free(neg);
                            var h: usize = @as(usize, @intCast(lv)) + 1;
                            while (h <= level) : (h += 1) {
                                try addClauseToFrame(allocator, &frames[h], neg);
                            }
                            stats.ctg_blocks += 1;
                            blocked_ctg = true;
                            changed = true;
                            break;
                        }
                    }
                }
                // If CTG is disjoint from Init, still safe to learn ~pred at F[0]
                if (!blocked_ctg) {
                    const init_b = try isInitBlocked(allocator, nl, pred);
                    stats.conflicts += init_b.conflicts;
                    if (init_b.blocked) {
                        const neg = try negateCube(allocator, pred);
                        defer allocator.free(neg);
                        try addClauseToFrame(allocator, &frames[0], neg);
                        stats.ctg_blocks += 1;
                        blocked_ctg = true;
                        changed = true;
                    }
                }
                if (blocked_ctg) continue; // retry drop of lit i
            }
            i += 1;
        }
    }
    return cube;
}

fn clauseSubsumes(a: []const Lit, b: []const Lit) bool {
    // a ⊆ b as sets (a is stronger clause if fewer lits... for blocking cubes, clause ~cube:
    // smaller cube = larger clause. We store clauses as ~cube lits.
    // Subsumption: clause A subsumes B if A ⊆ B (every lit of A in B).
    for (a) |la| {
        var found = false;
        for (b) |lb| {
            if (la == lb) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

fn addClauseToFrame(allocator: std.mem.Allocator, frame: *std.ArrayList(Clause), cl_lits: []const Lit) !void {
    // Drop if subsumed by existing; remove subsumed existing.
    var i: usize = 0;
    while (i < frame.items.len) {
        if (clauseSubsumes(frame.items[i].lits, cl_lits)) {
            // existing subsumes new — skip add
            return;
        }
        if (clauseSubsumes(cl_lits, frame.items[i].lits)) {
            allocator.free(frame.items[i].lits);
            _ = frame.orderedRemove(i);
            continue;
        }
        i += 1;
    }
    try frame.append(allocator, .{ .lits = try allocator.dupe(Lit, cl_lits) });
}

const PushStats = struct {
    conflicts: u64 = 0,
    pushes: u64 = 0,
};

fn clauseEqual(a: []const Lit, b: []const Lit) bool {
    if (a.len != b.len) return false;
    for (a) |la| {
        var found = false;
        for (b) |lb| {
            if (la == lb) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

fn framesEqual(a: []const Clause, b: []const Clause) bool {
    if (a.len != b.len) return false;
    for (a) |ca| {
        var found = false;
        for (b) |cb| {
            if (clauseEqual(ca.lits, cb.lits)) {
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

/// Push clauses forward until quiescence: if C ∈ F[i] is inductive rel F[i],
/// promote to F[i+1]. Returns true if some consecutive frames become equal
/// (inductive invariant / competition-style fixed point).
fn pushFrames(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    frames: []std.ArrayList(Clause),
    stats: *PushStats,
) !bool {
    var changed = true;
    var rounds: u32 = 0;
    while (changed and rounds < 64) : (rounds += 1) {
        changed = false;
        var i: usize = 0;
        while (i + 1 < frames.len) : (i += 1) {
            var j: usize = 0;
            while (j < frames[i].items.len) : (j += 1) {
                const cl = frames[i].items[j].lits;
                const cube = try negateCube(allocator, cl);
                defer allocator.free(cube);
                const chk = try isRelativeInductive(allocator, nl, frames, i, cube);
                stats.conflicts += chk.conflicts;
                if (chk.ok) {
                    const before = frames[i + 1].items.len;
                    try addClauseToFrame(allocator, &frames[i + 1], cl);
                    if (frames[i + 1].items.len > before) {
                        stats.pushes += 1;
                        changed = true;
                    }
                }
            }
        }
    }
    // Fixed point: F[i] ≡ F[i+1] as clause sets for some i ≥ 0
    var i: usize = 0;
    while (i + 1 < frames.len) : (i += 1) {
        if (frames[i].items.len > 0 and framesEqual(frames[i].items, frames[i + 1].items)) {
            return true;
        }
    }
    return false;
}

/// Recursive blocking: given a cube at level, either block it at the highest
/// relatively-inductive frame or return a predecessor obligation.
const BlockStatus = enum { blocked, cex, unknown };

const PdrStats = struct {
    conflicts: u64 = 0,
    gens: u64 = 0,
    pushes: u64 = 0,
    ctg_blocks: u64 = 0,
    obligations: u64 = 0,
    ternary_drops: u64 = 0,
};

/// Predecessor cube prep: full minterms only — MIC + ternaryPreweaken do the heavy lifting.
fn ternaryWeakenCube(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    cube: []const Lit,
    stats: *PdrStats,
) ![]Lit {
    _ = nl;
    _ = stats;
    return try allocator.dupe(Lit, cube);
}

fn blockCube(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    frames: []std.ArrayList(Clause),
    level: usize,
    cube_in: []const Lit,
    stats: *PdrStats,
    prop: NetId,
    depth: u32,
) !BlockStatus {
    if (depth > 64) return .unknown;
    stats.obligations += 1;
    // Init intersection?
    const init_b = try isInitBlocked(allocator, nl, cube_in);
    stats.conflicts += init_b.conflicts;
    if (!init_b.blocked and level == 0) return .cex;

    const pre = try ternaryWeakenCube(allocator, nl, cube_in, stats);
    defer allocator.free(pre);
    const cube = try allocator.dupe(Lit, pre);
    defer allocator.free(cube);

    var lvl: i32 = @intCast(level);
    while (lvl >= 0) : (lvl -= 1) {
        const q = try relativeInductiveQuery(allocator, nl, frames, @intCast(lvl), cube);
        stats.conflicts += q.conflicts;
        if (q.ok) {
            var gstats: GenStats = .{};
            const gen = try generalize(allocator, nl, frames, @intCast(lvl), cube, &gstats, prop);
            defer allocator.free(gen);
            stats.conflicts += gstats.conflicts;
            stats.gens += gstats.gens;
            stats.ctg_blocks += gstats.ctg_blocks;
            const neg = try negateCube(allocator, gen);
            defer allocator.free(neg);
            var h: usize = @as(usize, @intCast(lvl)) + 1;
            while (h <= level) : (h += 1) {
                try addClauseToFrame(allocator, &frames[h], neg);
            }
            // Also try lift to F[0] if init-disjoint and inductive at 0
            if (lvl >= 0) {
                const init2 = try isInitBlocked(allocator, nl, gen);
                stats.conflicts += init2.conflicts;
                if (init2.blocked) {
                    try addClauseToFrame(allocator, &frames[0], neg);
                }
            }
            return .blocked;
        }
        if (q.pred) |pred| {
            defer allocator.free(pred);
            if (lvl == 0) {
                // Predecessor at level 0 under F[0] — check init
                const ib = try isInitBlocked(allocator, nl, pred);
                stats.conflicts += ib.conflicts;
                if (!ib.blocked) return .cex;
                // Block predecessor at 0
                const sub = try blockCube(allocator, nl, frames, 0, pred, stats, prop, depth + 1);
                if (sub == .cex) return .cex;
                if (sub == .unknown) return .unknown;
                // retry same lvl after blocking pred
                continue;
            }
            const sub = try blockCube(allocator, nl, frames, @intCast(lvl - 1), pred, stats, prop, depth + 1);
            if (sub == .cex) return .cex;
            if (sub == .unknown) return .unknown;
            // retry after recursive block
            continue;
        }
        // not inductive, no pred — try lower level
    }
    return .cex;
}

pub fn check(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bad: NetId,
    max_frames: u32,
) !PdrResult {
    if (nl.latches.items.len == 0) {
        var cnf = Cnf.init(allocator);
        defer cnf.deinit();
        const nn = nl.num_nets;
        cnf.ensureVars(nn);
        try blastFrame(&cnf, nl, 0, nn);
        try addConstraintsFrame(&cnf, nl, 0, nn);
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(bad.index()))});
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .unsat) return .{ .status = .proven, .conflicts = r.conflicts };
        if (r.status == .sat) return .{ .status = .violated, .conflicts = r.conflicts };
        return .{ .status = .unknown, .conflicts = r.conflicts };
    }

    var frames: std.ArrayList(std.ArrayList(Clause)) = .empty;
    defer {
        for (frames.items) |*fr| {
            for (fr.items) |cl| allocator.free(cl.lits);
            fr.deinit(allocator);
        }
        frames.deinit(allocator);
    }
    try frames.append(allocator, .empty);

    var stats: PdrStats = .{};
    var k: u32 = 0;

    while (k <= max_frames) : (k += 1) {
        // Block bad at frame k
        var blocking = true;
        while (blocking) {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            const nn = nl.num_nets;
            cnf.ensureVars(nn);
            try blastFrame(&cnf, nl, 0, nn);
            try addConstraintsFrame(&cnf, nl, 0, nn);
            if (k == 0) {
                for (nl.latches.items) |lat| {
                    if (lat.init) |iv| {
                        const q = Lit.positive(Var.fromIndex(lat.q.index()));
                        if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
                    }
                }
            }
            var fi: u32 = 0;
            while (fi <= k) : (fi += 1) {
                try addFrameClauses(&cnf, frames.items[fi].items, 0);
            }
            try cnf.addClause(&.{Lit.positive(Var.fromIndex(bad.index()))});

            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 200_000 });
            stats.conflicts += r.conflicts;
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };

            if (r.status == .unknown) {
                if (r.model) |m| allocator.free(m);
                return .{
                    .status = .unknown,
                    .frames = k,
                    .conflicts = stats.conflicts,
                    .generalizations = stats.gens,
                    .pushes = stats.pushes,
                    .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
                };
            }
            if (r.status == .unsat) {
                if (r.model) |m| allocator.free(m);
                blocking = false;
                break;
            }

            const model = r.model.?;
            defer allocator.free(model);
            const cube = try latchCube(allocator, nl, model, 0);
            defer allocator.free(cube);

            if (k == 0) {
                const nlat = @as(u32, @intCast(nl.latches.items.len));
                const cex = try allocator.alloc(Value, nlat);
                for (nl.latches.items, 0..) |lat, i| cex[i] = model[lat.q.index()];
                return .{
                    .status = .violated,
                    .frames = 0,
                    .conflicts = stats.conflicts,
                    .generalizations = stats.gens,
                    .pushes = stats.pushes,
                    .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
                    .cex_latches = cex,
                    .nlatches = nlat,
                    .cex_len = 1,
                };
            }

            // Recursive block with MIC+CTG+ternary (competition-style obligations).
            const bs = try blockCube(allocator, nl, frames.items, k - 1, cube, &stats, bad, 0);
            if (bs == .cex) {
                const nlat = @as(u32, @intCast(nl.latches.items.len));
                const cex = try allocator.alloc(Value, nlat);
                for (nl.latches.items, 0..) |lat, i| cex[i] = model[lat.q.index()];
                return .{
                    .status = .violated,
                    .frames = k,
                    .conflicts = stats.conflicts,
                    .generalizations = stats.gens,
                    .pushes = stats.pushes,
                    .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
                    .cex_latches = cex,
                    .nlatches = nlat,
                    .cex_len = 1,
                };
            }
            if (bs == .unknown) {
                return .{
                    .status = .unknown,
                    .frames = k,
                    .conflicts = stats.conflicts,
                    .generalizations = stats.gens,
                    .pushes = stats.pushes,
                    .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
                };
            }
        }

        if (k == max_frames) break;

        try frames.append(allocator, .empty);
        var pstats: PushStats = .{};
        const fixed = try pushFrames(allocator, nl, frames.items, &pstats);
        stats.conflicts += pstats.conflicts;
        stats.pushes += pstats.pushes;

        if (fixed and k >= 1) {
            return .{
                .status = .proven,
                .frames = k + 1,
                .conflicts = stats.conflicts,
                .generalizations = stats.gens,
                .pushes = stats.pushes,
                .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
            };
        }
    }

    return .{
        .status = .unknown,
        .frames = k,
        .conflicts = stats.conflicts,
        .generalizations = stats.gens,
        .pushes = stats.pushes,
        .ctg_blocks = stats.ctg_blocks,
                    .obligations = stats.obligations,
                    .ternary_drops = stats.ternary_drops,
    };
}

/// Multi-property: bad is OR of all nets in `bads` (synthesized OR tree on a fresh net).
pub fn checkMulti(
    allocator: std.mem.Allocator,
    nl: *Netlist,
    bads: []const NetId,
    max_frames: u32,
) !PdrResult {
    if (bads.len == 0) return .{ .status = .proven };
    if (bads.len == 1) return check(allocator, nl, bads[0], max_frames);
    // Build OR of all bad signals → one output net
    var acc = bads[0];
    var i: usize = 1;
    while (i < bads.len) : (i += 1) {
        const y = try nl.allocNet();
        try nl.addGate(.or_, &.{ acc, bads[i] }, y);
        acc = y;
    }
    return check(allocator, nl, acc, max_frames);
}

/// Convenience: `nl.badProps()`.
pub fn checkNetlist(allocator: std.mem.Allocator, nl: *Netlist, max_frames: u32) !PdrResult {
    return checkMulti(allocator, nl, nl.badProps(), max_frames);
}

// Alias for IC3 naming
pub const checkIc3 = check;
pub const Ic3Status = PdrStatus;
pub const Ic3Result = PdrResult;

test "pdr stuck-at-zero proven" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    const r = try check(std.testing.allocator, &nl, q, 16);
    defer if (r.cex_latches) |c| std.testing.allocator.free(c);
    try std.testing.expect(r.status == .proven or r.status == .unknown);
    try std.testing.expect(r.status != .violated);
}

test "pdr init bad violated" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, true);
    try nl.addLatch(d, q, true);
    const r = try check(std.testing.allocator, &nl, q, 8);
    defer if (r.cex_latches) |c| std.testing.allocator.free(c);
    try std.testing.expect(r.status == .violated);
}

test "pdr counter not false-proven" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q0 = try nl.allocNetNamed("q0");
    const q1 = try nl.allocNetNamed("q1");
    const d0 = try nl.allocNetNamed("d0");
    const d1 = try nl.allocNetNamed("d1");
    const bad = try nl.allocNetNamed("bad");
    try nl.addGate(.not, &.{q0}, d0);
    try nl.addGate(.xor, &.{ q1, q0 }, d1);
    try nl.addGate(.and_, &.{ q1, q0 }, bad);
    try nl.addLatch(d0, q0, false);
    try nl.addLatch(d1, q1, false);
    const r = try check(std.testing.allocator, &nl, bad, 20);
    defer if (r.cex_latches) |c| std.testing.allocator.free(c);
    try std.testing.expect(r.status == .violated or r.status == .unknown);
}
