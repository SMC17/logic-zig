//! CDCL SAT solver: 2-watched literals, 1-UIP learning, non-chronological
//! backjump, VSIDS, phase saving, optional RUP/DRAT-style proof log.
//!
//! Correctness contract:
//! - SAT ⇒ model validates via `Cnf.checkModel` against original formula clauses
//! - UNSAT (unlimited) ⇒ exhaustive under CDCL; optional RUP proof checks
//! - `unknown` only when `max_conflicts` hit

const std = @import("std");
const cnf_mod = @import("cnf.zig");
const lit_mod = @import("../core/lit.zig");
const drat_mod = @import("drat.zig");

const Cnf = cnf_mod.Cnf;
const ClauseId = cnf_mod.ClauseId;
const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Value = lit_mod.Value;

pub const SolveStatus = enum { sat, unsat, unknown };

pub const SolveResult = struct {
    status: SolveStatus,
    model: ?[]Value = null,
    conflicts: u64 = 0,
    decisions: u64 = 0,
    propagations: u64 = 0,
    learned: u64 = 0,
    reduced: u64 = 0,
    /// Owned RUP proof lines (clause additions) when proof logging enabled; free with deinitProof.
    proof: ?drat_mod.Proof = null,
    /// After unsat under assumptions: minimal assumption core (owned dimacs lits); free with allocator.free.
    assumption_core: ?[]i32 = null,
    /// True when `assumption_core` is the unique MUS of the assumption set.
    assumption_core_unique: bool = false,
};

pub const SolverOptions = struct {
    max_conflicts: u64 = std.math.maxInt(u64),
    complete_model: bool = true,
    /// Emit RUP clause-addition proof on the way (checked for UNSAT).
    proof: bool = false,
    var_decay: f64 = 0.95,
    clause_decay: f64 = 0.999,
    /// Restart base in conflicts (0 = no restarts).
    restart_base: u64 = 50,
    /// Reduce learned DB every N conflicts (0 = never).
    reduce_interval: u64 = 1500,
    /// Keep at least this many learned clauses after reduce.
    reduce_keep_min: u32 = 100,
    /// Prefer deleting high-LBD clauses (Glucose-style).
    reduce_by_lbd: bool = true,
    /// Simple local conflict-clause minimization.
    minimize: bool = true,
    /// Never delete learned clauses with LBD <= this (Glucose glue tiers).
    keep_lbd_max: u16 = 2,
    /// Rephase saved polarities every N restarts (0 = never).
    rephase_interval: u32 = 3,
    /// Run pure-literal elimination once after initial units (non-assumption solve only).
    /// Default off: level-0 pure pins interact poorly with multi-shot reuse.
    pure_literal: bool = false,
};

const ClauseRange = struct {
    start: u32,
    len: u32,
    learned: bool,
    deleted: bool = false,
    activity: f64,
    /// Literal block distance (Glucose-style); 0 = unknown / problem clause.
    lbd: u16 = 0,
};

pub const Solver = struct {
    allocator: std.mem.Allocator,
    /// Original clause count (indices < this are problem clauses).
    orig_clauses: u32,
    num_vars: u32,
    opts: SolverOptions,

    lits: std.ArrayList(Lit) = .empty,
    clauses: std.ArrayList(ClauseRange) = .empty,

    assign: []Value,
    reason: []?ClauseId,
    level: []i32,
    trail: std.ArrayList(Lit) = .empty,
    trail_lim: std.ArrayList(u32) = .empty,
    watches: []std.ArrayList(ClauseId),
    qhead: usize = 0,

    activity: []f64,
    phase: []bool,
    var_inc: f64 = 1.0,
    cla_inc: f64 = 1.0,

    /// Max-heap of variable indices by activity (VSIDS).
    order_heap: std.ArrayList(u32) = .empty,
    /// heap index of var, or -1 if not in heap.
    heap_pos: []i32,

    seen: []bool,
    analyze_to_clear: std.ArrayList(u32) = .empty,
    learnt_buf: std.ArrayList(Lit) = .empty,

    conflict_count: u64 = 0,
    decision_count: u64 = 0,
    prop_count: u64 = 0,
    learned_count: u64 = 0,
    reduced_count: u64 = 0,
    compact_count: u64 = 0,
    rephase_count: u64 = 0,
    pure_assign_count: u64 = 0,
    /// Assumption decision levels (for multi-shot): restart only back to this.
    assumption_level: i32 = 0,

    proof: ?drat_mod.Proof = null,
    /// Snapshot of original problem for model check (not including learned).
    orig_cnf: Cnf,

    pub fn init(allocator: std.mem.Allocator, cnf: *const Cnf, opts: SolverOptions) !Solver {
        const n = cnf.num_vars;
        const assign = try allocator.alloc(Value, n);
        errdefer allocator.free(assign);
        @memset(assign, .undef);

        const reason = try allocator.alloc(?ClauseId, n);
        errdefer allocator.free(reason);
        @memset(reason, null);

        const level = try allocator.alloc(i32, n);
        errdefer allocator.free(level);
        @memset(level, -1);

        const activity = try allocator.alloc(f64, n);
        errdefer allocator.free(activity);
        @memset(activity, 0);

        const phase = try allocator.alloc(bool, n);
        errdefer allocator.free(phase);
        @memset(phase, true);

        const seen = try allocator.alloc(bool, n);
        errdefer allocator.free(seen);
        @memset(seen, false);

        const heap_pos = try allocator.alloc(i32, n);
        errdefer allocator.free(heap_pos);
        @memset(heap_pos, -1);

        const watches = try allocator.alloc(std.ArrayList(ClauseId), if (n == 0) 0 else n * 2);
        errdefer allocator.free(watches);
        for (watches) |*w| w.* = .empty;

        var s = Solver{
            .allocator = allocator,
            .orig_clauses = cnf.numClauses(),
            .num_vars = n,
            .opts = opts,
            .assign = assign,
            .reason = reason,
            .level = level,
            .activity = activity,
            .phase = phase,
            .heap_pos = heap_pos,
            .seen = seen,
            .watches = watches,
            .orig_cnf = Cnf.init(allocator),
        };
        errdefer s.orig_cnf.deinit();
        // Preserve declared var count even when free vars have no clauses
        // (IPASIR may assume on vars never mentioned in permanent clauses).
        s.orig_cnf.ensureVars(n);

        // Seed VSIDS heap with all variables.
        var vi: u32 = 0;
        while (vi < n) : (vi += 1) {
            try s.heapInsert(vi);
        }

        // Pre-size trail / clause storage for fewer reallocs on medium CNFs.
        const nc = cnf.numClauses();
        try s.trail.ensureTotalCapacity(allocator, n + 8);
        try s.lits.ensureTotalCapacity(allocator, nc * 3 + 16);
        try s.clauses.ensureTotalCapacity(allocator, nc + 16);
        // Rough watch density: 2 watches per clause → reserve ~2*nc/n per list.
        const per_watch: usize = @max(4, (nc * 2) / @max(n * 2, 1) + 2);
        for (s.watches) |*w| {
            try w.ensureTotalCapacity(allocator, per_watch);
        }

        // Copy original clauses into DB + orig_cnf.
        for (0..cnf.numClauses()) |ci| {
            const cl = cnf.clauseSlice(ClauseId.fromIndex(@intCast(ci)));
            try s.orig_cnf.addClause(cl);
            _ = try s.addClauseRaw(cl, false);
        }
        s.orig_cnf.ensureVars(n);

        // Jeroslow-Wang initial VSIDS activity + preferred phase.
        s.initJwHeuristic();

        if (opts.proof) {
            s.proof = drat_mod.Proof.init(allocator);
        }
        return s;
    }

    /// Seed activity with 2^{-|C|} per occurrence; phase = majority polarity weight.
    fn initJwHeuristic(self: *Solver) void {
        if (self.num_vars == 0) return;
        var pos_w = self.allocator.alloc(f64, self.num_vars) catch return;
        defer self.allocator.free(pos_w);
        var neg_w = self.allocator.alloc(f64, self.num_vars) catch return;
        defer self.allocator.free(neg_w);
        @memset(pos_w, 0);
        @memset(neg_w, 0);

        for (0..self.clauses.items.len) |ci| {
            const id = ClauseId.fromIndex(@intCast(ci));
            if (self.isDeleted(id)) continue;
            const cl = self.clauseSlice(id);
            if (cl.len == 0) continue;
            // weight = 2^{-len}, clamp len for underflow
            const len_c: u32 = @min(cl.len, 24);
            const w = std.math.exp2(-@as(f64, @floatFromInt(len_c)));
            for (cl) |l| {
                const v = l.variable().index();
                if (v >= self.num_vars) continue;
                if (l.isNeg()) {
                    neg_w[v] += w;
                } else {
                    pos_w[v] += w;
                }
                self.activity[v] += w;
            }
        }
        var vi: u32 = 0;
        while (vi < self.num_vars) : (vi += 1) {
            // Prefer the heavier polarity as the saved phase (true = positive).
            self.phase[vi] = pos_w[vi] >= neg_w[vi];
            if (self.heap_pos[vi] >= 0) {
                self.heapBubbleUp(@intCast(self.heap_pos[vi]));
            }
        }
    }

    pub fn deinit(self: *Solver) void {
        for (self.watches) |*w| w.deinit(self.allocator);
        self.allocator.free(self.watches);
        self.allocator.free(self.assign);
        self.allocator.free(self.reason);
        self.allocator.free(self.level);
        self.allocator.free(self.activity);
        self.allocator.free(self.phase);
        self.allocator.free(self.heap_pos);
        self.allocator.free(self.seen);
        self.trail.deinit(self.allocator);
        self.trail_lim.deinit(self.allocator);
        self.order_heap.deinit(self.allocator);
        self.lits.deinit(self.allocator);
        self.clauses.deinit(self.allocator);
        self.analyze_to_clear.deinit(self.allocator);
        self.learnt_buf.deinit(self.allocator);
        if (self.proof) |*p| p.deinit();
        self.orig_cnf.deinit();
        self.* = undefined;
    }

    // ---- VSIDS max-heap ----------------------------------------------------

    fn heapLt(self: *const Solver, a: u32, b: u32) bool {
        // Max-heap: higher activity is "less" for sift so top is largest... use greater.
        return self.activity[a] > self.activity[b];
    }

    fn heapInsert(self: *Solver, v: u32) !void {
        if (self.heap_pos[v] != -1) return;
        try self.order_heap.append(self.allocator, v);
        self.heap_pos[v] = @intCast(self.order_heap.items.len - 1);
        self.heapBubbleUp(@intCast(self.order_heap.items.len - 1));
    }

    fn heapBubbleUp(self: *Solver, start: usize) void {
        var i = start;
        while (i > 0) {
            const parent = (i - 1) / 2;
            const vi = self.order_heap.items[i];
            const vp = self.order_heap.items[parent];
            if (!self.heapLt(vi, vp)) break;
            self.order_heap.items[i] = vp;
            self.order_heap.items[parent] = vi;
            self.heap_pos[vp] = @intCast(i);
            self.heap_pos[vi] = @intCast(parent);
            i = parent;
        }
    }

    fn heapBubbleDown(self: *Solver, start: usize) void {
        var i = start;
        const n = self.order_heap.items.len;
        while (true) {
            var best = i;
            const l = 2 * i + 1;
            const r = 2 * i + 2;
            if (l < n and self.heapLt(self.order_heap.items[l], self.order_heap.items[best])) best = l;
            if (r < n and self.heapLt(self.order_heap.items[r], self.order_heap.items[best])) best = r;
            if (best == i) break;
            const a = self.order_heap.items[i];
            const b = self.order_heap.items[best];
            self.order_heap.items[i] = b;
            self.order_heap.items[best] = a;
            self.heap_pos[b] = @intCast(i);
            self.heap_pos[a] = @intCast(best);
            i = best;
        }
    }

    fn heapRemove(self: *Solver, v: u32) void {
        const pos = self.heap_pos[v];
        if (pos < 0) return;
        const last = self.order_heap.items.len - 1;
        const pi: usize = @intCast(pos);
        self.heap_pos[v] = -1;
        if (pi == last) {
            _ = self.order_heap.pop();
            return;
        }
        const moved = self.order_heap.items[last];
        _ = self.order_heap.pop();
        self.order_heap.items[pi] = moved;
        self.heap_pos[moved] = @intCast(pi);
        self.heapBubbleUp(pi);
        self.heapBubbleDown(pi);
    }

    fn heapIncrease(self: *Solver, v: u32) void {
        if (self.heap_pos[v] >= 0) {
            self.heapBubbleUp(@intCast(self.heap_pos[v]));
        } else {
            self.heapInsert(v) catch {};
        }
    }

    fn clauseSlice(self: *const Solver, id: ClauseId) []const Lit {
        const r = self.clauses.items[id.index()];
        return self.lits.items[r.start .. r.start + r.len];
    }

    fn clauseSliceMut(self: *Solver, id: ClauseId) []Lit {
        const r = self.clauses.items[id.index()];
        return self.lits.items[r.start .. r.start + r.len];
    }

    fn addClauseRaw(self: *Solver, clause: []const Lit, learned: bool) !ClauseId {
        // Dedup into a stack buffer / local list — never alias `learnt_buf` if
        // `clause` is a slice of it (analyze → learn path).
        var tmp: std.ArrayList(Lit) = .empty;
        defer tmp.deinit(self.allocator);

        for (clause) |l| {
            var taut = false;
            var dup = false;
            for (tmp.items) |e| {
                if (e == l) dup = true;
                if (e == l.not()) taut = true;
            }
            if (taut) {
                // Skip tautological learned clauses (should be rare).
                if (self.clauses.items.len > 0) return ClauseId.fromIndex(0);
                // Fall through to empty.
                tmp.clearRetainingCapacity();
                break;
            }
            if (!dup) try tmp.append(self.allocator, l);
        }

        const start: u32 = @intCast(self.lits.items.len);
        try self.lits.appendSlice(self.allocator, tmp.items);
        const id = ClauseId.fromIndex(@intCast(self.clauses.items.len));
        try self.clauses.append(self.allocator, .{
            .start = start,
            .len = @intCast(tmp.items.len),
            .learned = learned,
            .deleted = false,
            .activity = 0,
            .lbd = 0,
        });

        const cl = self.clauseSlice(id);
        if (cl.len >= 1 and self.num_vars > 0) {
            const wi0 = cl[0].watchIndex();
            std.debug.assert(wi0 < self.watches.len);
            try self.watches[wi0].append(self.allocator, id);
            if (cl.len >= 2) {
                const wi1 = cl[1].watchIndex();
                std.debug.assert(wi1 < self.watches.len);
                try self.watches[wi1].append(self.allocator, id);
            }
        }
        return id;
    }

    fn isDeleted(self: *const Solver, id: ClauseId) bool {
        return self.clauses.items[id.index()].deleted;
    }

    fn decisionLevel(self: *const Solver) i32 {
        return @intCast(self.trail_lim.items.len);
    }

    /// Hot-path lit value: avoid call overhead of evalLit.
    inline fn valueLit(self: *const Solver, l: Lit) Value {
        const raw = @intFromEnum(l);
        const a = self.assign[raw >> 1];
        if (a == .undef) return .undef;
        // Positive lit true iff assign true; negative lit true iff assign false.
        if ((raw & 1) == 0) return a;
        return if (a == .true_) .false_ else .true_;
    }

    inline fn isTrueLit(self: *const Solver, l: Lit) bool {
        return self.valueLit(l) == .true_;
    }

    inline fn isFalseLit(self: *const Solver, l: Lit) bool {
        return self.valueLit(l) == .false_;
    }

    fn enqueue(self: *Solver, l: Lit, reason: ?ClauseId) bool {
        const raw = @intFromEnum(l);
        const v = raw >> 1;
        const want: Value = if ((raw & 1) == 1) .false_ else .true_;
        const cur = self.assign[v];
        if (cur != .undef) return cur == want;
        self.assign[v] = want;
        self.reason[v] = reason;
        self.level[v] = self.decisionLevel();
        self.phase[v] = (raw & 1) == 0;
        self.trail.append(self.allocator, l) catch return false;
        self.prop_count += 1;
        return true;
    }

    fn propagate(self: *Solver) ?ClauseId {
        while (self.qhead < self.trail.items.len) {
            const p = self.trail.items[self.qhead];
            self.qhead += 1;
            const false_lit = p.not();
            var ws = &self.watches[@intFromEnum(false_lit)];
            var i: usize = 0;
            while (i < ws.items.len) {
                const cid = ws.items[i];
                const cr = self.clauses.items[cid.index()];
                if (cr.deleted) {
                    _ = ws.swapRemove(i);
                    continue;
                }
                const cl = self.lits.items[cr.start .. cr.start + cr.len];

                if (cl.len == 0) return cid;

                // --- unit ---
                if (cl.len == 1) {
                    switch (self.valueLit(cl[0])) {
                        .true_ => i += 1,
                        .false_ => return cid,
                        .undef => {
                            if (!self.enqueue(cl[0], cid)) return cid;
                            i += 1;
                        },
                    }
                    continue;
                }

                // --- binary fast path (majority of watches on industrial CNF) ---
                // Invariant for 1-UIP: reason clauses keep asserting lit at [0].
                if (cr.len == 2) {
                    const clm = self.clauseSliceMut(cid);
                    if (clm[0] == false_lit) {
                        std.mem.swap(Lit, &clm[0], &clm[1]);
                    } else if (clm[1] != false_lit) {
                        i += 1; // stale
                        continue;
                    }
                    // Now clm[1] == false_lit, clm[0] is the other lit.
                    switch (self.valueLit(clm[0])) {
                        .true_ => i += 1,
                        .false_ => return cid,
                        .undef => {
                            if (!self.enqueue(clm[0], cid)) return cid;
                            i += 1;
                        },
                    }
                    continue;
                }

                // --- long clause ---
                const clm = self.clauseSliceMut(cid);
                if (clm[0] == false_lit) {
                    std.mem.swap(Lit, &clm[0], &clm[1]);
                }
                if (clm[1] != false_lit) {
                    i += 1;
                    continue;
                }

                const first = clm[0];
                if (self.isTrueLit(first)) {
                    i += 1;
                    continue;
                }

                var found = false;
                var k: usize = 2;
                while (k < clm.len) : (k += 1) {
                    if (!self.isFalseLit(clm[k])) {
                        clm[1] = clm[k];
                        clm[k] = false_lit;
                        _ = ws.swapRemove(i);
                        self.watches[@intFromEnum(clm[1])].append(self.allocator, cid) catch return cid;
                        found = true;
                        break;
                    }
                }
                if (found) continue;

                if (self.isFalseLit(first)) return cid;
                if (!self.enqueue(first, cid)) return cid;
                i += 1;
            }
        }
        return null;
    }

    fn cancelUntil(self: *Solver, lvl: i32) void {
        std.debug.assert(lvl >= 0);
        while (self.decisionLevel() > lvl) {
            const start: usize = self.trail_lim.items[self.trail_lim.items.len - 1];
            _ = self.trail_lim.pop();
            while (self.trail.items.len > start) {
                const lit = self.trail.pop().?;
                const v = lit.variable().index();
                self.assign[v] = .undef;
                self.reason[v] = null;
                self.level[v] = -1;
                // Return to VSIDS heap for future branching.
                self.heapInsert(v) catch {};
            }
        }
        self.qhead = self.trail.items.len;
    }

    fn varBump(self: *Solver, v: u32) void {
        self.activity[v] += self.var_inc;
        if (self.activity[v] > 1e100) {
            // Rescale.
            for (self.activity) |*a| a.* *= 1e-100;
            self.var_inc *= 1e-100;
            // Rebuild heap order after rescale.
            for (self.order_heap.items, 0..) |_, i| {
                self.heapBubbleDown(i);
            }
        }
        self.heapIncrease(v);
    }

    fn varDecay(self: *Solver) void {
        self.var_inc /= self.opts.var_decay;
    }

    fn claBump(self: *Solver, id: ClauseId) void {
        const r = &self.clauses.items[id.index()];
        if (!r.learned) return;
        r.activity += self.cla_inc;
        if (r.activity > 1e100) {
            for (self.clauses.items) |*c| {
                if (c.learned) c.activity *= 1e-100;
            }
            self.cla_inc *= 1e-100;
        }
    }

    fn claDecay(self: *Solver) void {
        self.cla_inc /= self.opts.clause_decay;
    }

    /// 1-UIP conflict analysis. Writes asserting clause into learnt_buf (UIP at [0]).
    /// Returns backjump level.
    fn analyze(self: *Solver, conflict: ClauseId) !i32 {
        self.learnt_buf.clearRetainingCapacity();
        try self.learnt_buf.append(self.allocator, undefined); // placeholder for UIP

        const curr_level = self.decisionLevel();
        var pathC: i32 = 0;
        var p: ?Lit = null;
        var index: i32 = @intCast(self.trail.items.len - 1);
        var clause_id: ClauseId = conflict;

        self.analyze_to_clear.clearRetainingCapacity();

        while (true) {
            self.claBump(clause_id);
            const cl = self.clauseSlice(clause_id);
            const start: usize = if (p == null) 0 else 1;
            var i = start;
            while (i < cl.len) : (i += 1) {
                const lit = cl[i];
                const v = lit.variable().index();
                if (self.seen[v] or self.level[v] <= 0) continue;
                self.seen[v] = true;
                try self.analyze_to_clear.append(self.allocator, v);
                self.varBump(v);
                if (self.level[v] >= curr_level) {
                    pathC += 1;
                } else {
                    try self.learnt_buf.append(self.allocator, lit);
                }
            }

            // Next trail lit that is seen.
            while (true) {
                std.debug.assert(index >= 0);
                const tlit = self.trail.items[@intCast(index)];
                index -= 1;
                const v = tlit.variable().index();
                if (self.seen[v]) {
                    p = tlit;
                    break;
                }
            }

            const pv = p.?.variable().index();
            self.seen[pv] = false;
            pathC -= 1;
            if (pathC <= 0) break;

            clause_id = self.reason[pv] orelse {
                // Decision lit at conflict level without reason — shouldn't for pathC>0 after first.
                break;
            };
        }

        // UIP is ~p
        self.learnt_buf.items[0] = p.?.not();

        // Clear seen for analyze
        for (self.analyze_to_clear.items) |v| self.seen[v] = false;

        if (self.opts.minimize) {
            try self.minimizeLearnt();
        }

        // Backjump level: max level among lits after UIP; swap second watch to that lit.
        var bt: i32 = 0;
        if (self.learnt_buf.items.len > 1) {
            var max_i: usize = 1;
            bt = self.level[self.learnt_buf.items[1].variable().index()];
            var i: usize = 2;
            while (i < self.learnt_buf.items.len) : (i += 1) {
                const lv = self.level[self.learnt_buf.items[i].variable().index()];
                if (lv > bt) {
                    bt = lv;
                    max_i = i;
                }
            }
            if (max_i != 1) {
                std.mem.swap(Lit, &self.learnt_buf.items[1], &self.learnt_buf.items[max_i]);
            }
        }
        return bt;
    }

    /// Local minimization: drop lit if its reason's other lits are already in the learnt set.
    fn minimizeLearnt(self: *Solver) !void {
        if (self.learnt_buf.items.len <= 1) return;
        // Mark learnt vars
        @memset(self.seen, false);
        for (self.learnt_buf.items) |l| self.seen[l.variable().index()] = true;

        var write: usize = 1; // keep UIP at 0
        var i: usize = 1;
        while (i < self.learnt_buf.items.len) : (i += 1) {
            const lit = self.learnt_buf.items[i];
            const v = lit.variable().index();
            const reason = self.reason[v];
            var keep = true;
            if (reason) |rid| {
                if (!self.isDeleted(rid)) {
                    const cl = self.clauseSlice(rid);
                    var all_in = true;
                    for (cl) |rl| {
                        const rv = rl.variable().index();
                        if (rv == v) continue;
                        if (self.level[rv] == 0) continue;
                        if (!self.seen[rv]) {
                            all_in = false;
                            break;
                        }
                    }
                    if (all_in) keep = false;
                }
            }
            if (keep) {
                self.learnt_buf.items[write] = lit;
                write += 1;
            } else {
                self.seen[v] = false;
            }
        }
        self.learnt_buf.shrinkRetainingCapacity(write);
        @memset(self.seen, false);
    }

    fn computeLbd(self: *Solver, clause: []const Lit) u16 {
        // Stamp distinct decision levels using `seen` as a level-mark set (reused buffer).
        // Clear only touched levels via analyze_to_clear scratch of level ids stored as u32.
        var nlev: u16 = 0;
        var stamps: [64]u32 = undefined;
        var nstamp: usize = 0;
        for (clause) |l| {
            const lv = self.level[l.variable().index()];
            if (lv <= 0) continue;
            const key: u32 = @intCast(lv);
            // Linear stamp in small stack (LBD rarely > 8–12).
            var found = false;
            for (stamps[0..nstamp]) |e| {
                if (e == key) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                if (nstamp < stamps.len) {
                    stamps[nstamp] = key;
                    nstamp += 1;
                    nlev += 1;
                } else {
                    return nlev + 1;
                }
            }
        }
        return nlev;
    }

    fn pickBranch(self: *Solver) ?Lit {
        // VSIDS heap: pop assigned heads until unassigned.
        while (self.order_heap.items.len > 0) {
            const top = self.order_heap.items[0];
            if (self.assign[top] != .undef) {
                self.heapRemove(top);
                continue;
            }
            return Lit.make(Var.fromIndex(top), !self.phase[top]);
        }
        // Fallback scan (should be rare).
        var vi: u32 = 0;
        while (vi < self.num_vars) : (vi += 1) {
            if (self.assign[vi] == .undef) {
                return Lit.make(Var.fromIndex(vi), !self.phase[vi]);
            }
        }
        return null;
    }

    fn decide(self: *Solver, l: Lit) !void {
        try self.trail_lim.append(self.allocator, @intCast(self.trail.items.len));
        self.decision_count += 1;
        _ = self.enqueue(l, null);
    }

    /// MiniSat Luby unit at 0-based restart index `x`, scaled by restart_base.
    fn lubyUnits(x: u64) u64 {
        // Find finite subsequence containing index x.
        var size: u64 = 1;
        var seq: u64 = 0;
        while (size < x + 1) {
            seq += 1;
            size = 2 * size + 1;
        }
        var xx = x;
        while (size - 1 != xx) {
            size = (size - 1) >> 1;
            seq -= 1;
            xx = xx % size;
        }
        // 2^seq
        return @as(u64, 1) << @intCast(@min(seq, 63));
    }

    fn lubyLimit(self: *const Solver, restart_index: u64) u64 {
        const base = if (self.opts.restart_base == 0) @as(u64, 100) else self.opts.restart_base;
        return lubyUnits(restart_index) * base;
    }

    fn isLocked(self: *const Solver, id: ClauseId) bool {
        // Locked iff it is the reason for some trail literal (O(trail), not O(vars)).
        for (self.trail.items) |lit| {
            const v = lit.variable().index();
            if (self.reason[v]) |cid| {
                if (cid == id) return true;
            }
        }
        return false;
    }

    fn deleteClause(self: *Solver, id: ClauseId) void {
        const r = &self.clauses.items[id.index()];
        if (r.deleted or !r.learned) return;
        if (self.proof) |*pf| {
            const cl = self.clauseSlice(id);
            pf.delClause(cl) catch {};
        }
        r.deleted = true;
        self.reduced_count += 1;
        // Lazy detach: propagate skips deleted and swapRemoves from watch lists.
    }

    fn reduceDb(self: *Solver) void {
        // Drop high-LBD / low-activity learned clauses that are not trail reasons.
        // Keep glue clauses (LBD <= keep_lbd_max) permanently unless locked-delete path.
        var learned_ids: std.ArrayList(ClauseId) = .empty;
        defer learned_ids.deinit(self.allocator);
        for (self.clauses.items, 0..) |c, i| {
            if (c.learned and !c.deleted and c.len > 2) {
                if (c.lbd != 0 and c.lbd <= self.opts.keep_lbd_max) continue;
                const id = ClauseId.fromIndex(@intCast(i));
                if (!self.isLocked(id)) {
                    learned_ids.append(self.allocator, id) catch continue;
                }
            }
        }
        const min_keep = self.opts.reduce_keep_min;
        if (learned_ids.items.len <= min_keep) return;

        if (self.opts.reduce_by_lbd) {
            std.mem.sort(ClauseId, learned_ids.items, self, struct {
                fn less(s: *Solver, a: ClauseId, b: ClauseId) bool {
                    const ca = s.clauses.items[a.index()];
                    const cb = s.clauses.items[b.index()];
                    if (ca.lbd != cb.lbd) return ca.lbd > cb.lbd;
                    return ca.activity < cb.activity;
                }
            }.less);
        } else {
            std.mem.sort(ClauseId, learned_ids.items, self, struct {
                fn less(s: *Solver, a: ClauseId, b: ClauseId) bool {
                    return s.clauses.items[a.index()].activity < s.clauses.items[b.index()].activity;
                }
            }.less);
        }

        const can_drop = learned_ids.items.len - min_keep;
        const drop_n = @min(can_drop, learned_ids.items.len / 2);
        var i: usize = 0;
        while (i < drop_n) : (i += 1) {
            self.deleteClause(learned_ids.items[i]);
        }
        // Compact when many soft-deletes accumulate.
        if (self.reduced_count > 0 and self.reduced_count % 100 == 0) {
            self.compact() catch {};
        }
    }

    /// Assign pure literals at decision level 0 (after units already propagated).
    fn eliminatePureLiterals(self: *Solver) !bool {
        if (!self.opts.pure_literal or self.num_vars == 0) return true;
        var pos = try self.allocator.alloc(u32, self.num_vars);
        defer self.allocator.free(pos);
        var neg = try self.allocator.alloc(u32, self.num_vars);
        defer self.allocator.free(neg);
        @memset(pos, 0);
        @memset(neg, 0);

        for (0..self.clauses.items.len) |ci| {
            const id = ClauseId.fromIndex(@intCast(ci));
            if (self.isDeleted(id)) continue;
            const cl = self.clauseSlice(id);
            // Skip satisfied clauses under current trail.
            var sat = false;
            for (cl) |l| {
                if (self.valueLit(l) == .true_) {
                    sat = true;
                    break;
                }
            }
            if (sat) continue;
            for (cl) |l| {
                if (self.valueLit(l) == .false_) continue;
                const v = l.variable().index();
                if (l.isNeg()) neg[v] += 1 else pos[v] += 1;
            }
        }

        var progress = false;
        var vi: u32 = 0;
        while (vi < self.num_vars) : (vi += 1) {
            if (self.assign[vi] != .undef) continue;
            if (pos[vi] > 0 and neg[vi] == 0) {
                if (!self.enqueue(Lit.positive(Var.fromIndex(vi)), null)) return false;
                self.pure_assign_count += 1;
                progress = true;
            } else if (neg[vi] > 0 and pos[vi] == 0) {
                if (!self.enqueue(Lit.negative(Var.fromIndex(vi)), null)) return false;
                self.pure_assign_count += 1;
                progress = true;
            }
        }
        if (progress) {
            if (self.propagate()) |_| return false;
        }
        return true;
    }

    fn rephase(self: *Solver) void {
        if (self.opts.rephase_interval == 0) return;
        self.rephase_count += 1;
        const mode = self.rephase_count % 4;
        var vi: u32 = 0;
        while (vi < self.num_vars) : (vi += 1) {
            switch (mode) {
                0 => {}, // keep phase
                1 => self.phase[vi] = !self.phase[vi], // flip all
                2 => self.phase[vi] = true, // all positive
                else => self.phase[vi] = (vi & 1) == 0, // checkerboard
            }
        }
    }

    /// Rebuild clause database without deleted clauses; rebuild watches.
    pub fn compact(self: *Solver) !void {
        self.cancelUntil(0);
        // Clear all reasons (trail empty after cancel).
        @memset(self.reason, null);

        var new_lits: std.ArrayList(Lit) = .empty;
        errdefer new_lits.deinit(self.allocator);
        var new_clauses: std.ArrayList(ClauseRange) = .empty;
        errdefer new_clauses.deinit(self.allocator);

        // Map old clause id → new id for reason fix (all null now).
        for (self.clauses.items) |c| {
            if (c.deleted) continue;
            if (c.len == 0 and c.learned) continue;
            const start: u32 = @intCast(new_lits.items.len);
            const slice = self.lits.items[c.start .. c.start + c.len];
            try new_lits.appendSlice(self.allocator, slice);
            try new_clauses.append(self.allocator, .{
                .start = start,
                .len = c.len,
                .learned = c.learned,
                .deleted = false,
                .activity = c.activity,
                .lbd = c.lbd,
            });
        }

        self.lits.deinit(self.allocator);
        self.clauses.deinit(self.allocator);
        self.lits = new_lits;
        self.clauses = new_clauses;

        // Rebuild watches.
        for (self.watches) |*w| {
            w.clearRetainingCapacity();
        }
        for (self.clauses.items, 0..) |c, ci| {
            if (c.len == 0) continue;
            const id = ClauseId.fromIndex(@intCast(ci));
            const cl = self.clauseSlice(id);
            try self.watches[cl[0].watchIndex()].append(self.allocator, id);
            if (cl.len >= 2) {
                try self.watches[cl[1].watchIndex()].append(self.allocator, id);
            }
        }
        self.compact_count += 1;
        self.qhead = 0;
    }

    /// Multi-shot: add a permanent clause (keeps learned clauses).
    pub fn addClausePermanent(self: *Solver, clause: []const Lit) !void {
        self.cancelUntil(0);
        _ = try self.addClauseRaw(clause, false);
        try self.orig_cnf.addClause(clause);
    }

    /// Multi-shot solve with assumptions (kept as decision levels 1..a).
    /// On UNSAT, fills `assumption_core` with a **deletion-minimal** unsat core
    /// and sets `assumption_core_unique` when it is the unique MUS of the set.
    pub fn solveAssumptions(self: *Solver, assumptions: []const Lit) !SolveResult {
        var r = try self.solveAssumptionsRaw(assumptions);
        if (r.status == .unsat and assumptions.len > 0) {
            const extracted = try self.extractAssumptionMus(assumptions);
            r.assumption_core = extracted.core;
            r.assumption_core_unique = extracted.unique;
        }
        return r;
    }

    pub const MusResult = struct {
        /// Deletion-minimal unsat core (DIMACS lits), owned.
        core: []i32,
        /// True iff this is the **unique** MUS of the assumption set:
        /// ∀a∈MUS. assumptions\{a} is SAT.
        unique: bool,
    };

    /// Extract a MUS of `assumptions` and test uniqueness.
    pub fn extractAssumptionMus(self: *Solver, assumptions: []const Lit) !MusResult {
        const core_dimacs = try self.minimizeAssumptionCore(assumptions);
        errdefer self.allocator.free(core_dimacs);

        var core_lits: std.ArrayList(Lit) = .empty;
        defer core_lits.deinit(self.allocator);
        for (core_dimacs) |d| try core_lits.append(self.allocator, Lit.fromDimacs(d));

        // Uniqueness: for every a in MUS, full assumption set without a is SAT.
        var unique = true;
        for (core_lits.items) |drop| {
            var reduced: std.ArrayList(Lit) = .empty;
            defer reduced.deinit(self.allocator);
            for (assumptions) |a| {
                if (a.toDimacs() != drop.toDimacs()) try reduced.append(self.allocator, a);
            }
            self.hardReset();
            const r = try self.solveAssumptionsRaw(reduced.items);
            defer if (r.model) |m| self.allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .unsat) {
                unique = false;
                break;
            }
        }
        return .{ .core = core_dimacs, .unique = unique };
    }

    /// Full reset to decision level −1 / empty trail for a clean multi-shot probe.
    fn hardReset(self: *Solver) void {
        self.cancelUntil(0);
        // Drop root-level assignments too so probes are independent.
        while (self.trail.items.len > 0) {
            const lit = self.trail.pop().?;
            const v = lit.variable().index();
            self.assign[v] = .undef;
            self.reason[v] = null;
            self.level[v] = -1;
            self.heapInsert(v) catch {};
        }
        self.trail_lim.clearRetainingCapacity();
        self.qhead = 0;
        self.assumption_level = 0;
    }

    /// Verify that every member of `core` is necessary (deletion-minimal).
    pub fn isDeletionMinimalCore(self: *Solver, core: []const Lit) !bool {
        if (core.len == 0) {
            self.hardReset();
            const r = try self.solveAssumptionsRaw(&.{});
            defer if (r.model) |m| self.allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            return r.status == .unsat;
        }
        {
            self.hardReset();
            const r = try self.solveAssumptionsRaw(core);
            defer if (r.model) |m| self.allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status != .unsat) return false;
        }
        var i: usize = 0;
        while (i < core.len) : (i += 1) {
            var reduced: std.ArrayList(Lit) = .empty;
            defer reduced.deinit(self.allocator);
            for (core, 0..) |a, j| {
                if (j != i) try reduced.append(self.allocator, a);
            }
            self.hardReset();
            const r = try self.solveAssumptionsRaw(reduced.items);
            defer if (r.model) |m| self.allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .unsat) return false;
        }
        return true;
    }

    fn solveAssumptionsRaw(self: *Solver, assumptions: []const Lit) !SolveResult {
        self.cancelUntil(0);
        self.assumption_level = 0;
        self.qhead = 0;

        for (0..self.clauses.items.len) |ci| {
            const id = ClauseId.fromIndex(@intCast(ci));
            if (self.isDeleted(id)) continue;
            const cl = self.clauseSlice(id);
            if (cl.len == 0) return self.finishUnsat();
            if (cl.len == 1) {
                if (!self.enqueue(cl[0], id)) return self.finishUnsat();
            }
        }
        if (self.propagate()) |_| return self.finishUnsat();

        for (assumptions) |a| {
            switch (self.valueLit(a)) {
                .true_ => {},
                .false_ => return self.finishUnsat(),
                .undef => {
                    try self.decide(a);
                    if (self.propagate()) |_| {
                        if (self.decisionLevel() <= self.assumption_level + 1) {
                            // will set assumption_level below; for first assump level is 1
                        }
                        if (self.decisionLevel() >= 1) {
                            // conflict under current assumptions
                            return self.finishUnsat();
                        }
                    }
                },
            }
        }
        self.assumption_level = self.decisionLevel();
        // Do not pure-elim under assumptions: level-0 pure pins break multi-shot cores.
        return try self.searchLoop();
    }

    /// Deletion filter: drop assumptions that are not needed for unsat.
    /// Each probe hard-resets the trail so multi-shot state cannot poison the check.
    fn minimizeAssumptionCore(self: *Solver, assumptions: []const Lit) ![]i32 {
        var core: std.ArrayList(Lit) = .empty;
        defer core.deinit(self.allocator);
        try core.appendSlice(self.allocator, assumptions);

        var i: usize = 0;
        while (i < core.items.len) {
            var reduced: std.ArrayList(Lit) = .empty;
            defer reduced.deinit(self.allocator);
            for (core.items, 0..) |a, j| {
                if (j != i) try reduced.append(self.allocator, a);
            }
            self.hardReset();
            const r = try self.solveAssumptionsRaw(reduced.items);
            defer if (r.model) |m| self.allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .unsat) {
                _ = core.orderedRemove(i);
            } else {
                i += 1;
            }
        }

        const out = try self.allocator.alloc(i32, core.items.len);
        for (core.items, 0..) |a, j| out[j] = a.toDimacs();
        return out;
    }

    pub fn solve(self: *Solver) !SolveResult {
        self.assumption_level = 0;
        self.cancelUntil(0);
        self.qhead = 0;

        if (self.num_vars == 0) {
            for (0..self.clauses.items.len) |ci| {
                if (!self.isDeleted(ClauseId.fromIndex(@intCast(ci))) and
                    self.clauseSlice(ClauseId.fromIndex(@intCast(ci))).len == 0)
                {
                    return self.finishUnsat();
                }
            }
            return .{ .status = .sat, .model = try self.allocator.alloc(Value, 0) };
        }

        for (0..self.clauses.items.len) |ci| {
            const id = ClauseId.fromIndex(@intCast(ci));
            if (self.isDeleted(id)) continue;
            if (self.clauseSlice(id).len == 0) return self.finishUnsat();
        }

        for (0..self.clauses.items.len) |ci| {
            const id = ClauseId.fromIndex(@intCast(ci));
            if (self.isDeleted(id)) continue;
            const cl = self.clauseSlice(id);
            if (cl.len == 1) {
                if (!self.enqueue(cl[0], id)) return self.finishUnsat();
            }
        }
        if (self.propagate()) |_| return self.finishUnsat();
        if (!try self.eliminatePureLiterals()) return self.finishUnsat();
        return try self.searchLoop();
    }

    fn searchLoop(self: *Solver) !SolveResult {
        var conflicts_at_restart: u64 = 0;
        var restart_index: u64 = 0;
        var restart_lim: u64 = if (self.opts.restart_base == 0)
            std.math.maxInt(u64)
        else
            self.lubyLimit(0);

        while (true) {
            if (self.conflict_count >= self.opts.max_conflicts) {
                return .{
                    .status = .unknown,
                    .conflicts = self.conflict_count,
                    .decisions = self.decision_count,
                    .propagations = self.prop_count,
                    .learned = self.learned_count,
                    .reduced = self.reduced_count,
                };
            }

            if (self.propagate()) |confl| {
                self.conflict_count += 1;
                if (self.decisionLevel() <= self.assumption_level) {
                    // Conflict at/below assumptions → unsat under assumptions (or global).
                    return self.finishUnsat();
                }

                const bt_level = try self.analyze(confl);
                const bt = @max(bt_level, self.assumption_level);
                self.cancelUntil(bt);

                // Copy learnt before mutating buffers.
                const learnt_copy = try self.allocator.dupe(Lit, self.learnt_buf.items);
                defer self.allocator.free(learnt_copy);
                std.debug.assert(learnt_copy.len >= 1);

                const cid = try self.addClauseRaw(learnt_copy, true);
                self.learned_count += 1;
                self.clauses.items[cid.index()].lbd = self.computeLbd(learnt_copy);
                self.claBump(cid);

                if (self.proof) |*pf| {
                    try pf.addClause(learnt_copy);
                }

                // Asserting clause: learnt[0] is unit under current assign.
                _ = self.enqueue(learnt_copy[0], cid);
                self.varDecay();
                self.claDecay();

                if (self.opts.reduce_interval > 0 and self.conflict_count % self.opts.reduce_interval == 0) {
                    self.reduceDb();
                }

                if (self.opts.restart_base > 0) {
                    conflicts_at_restart += 1;
                    if (conflicts_at_restart >= restart_lim) {
                        self.cancelUntil(self.assumption_level);
                        // Re-prop after restart
                        self.qhead = self.trail.items.len;
                        conflicts_at_restart = 0;
                        restart_index += 1;
                        restart_lim = self.lubyLimit(restart_index);
                        if (self.opts.rephase_interval > 0 and
                            restart_index % self.opts.rephase_interval == 0)
                        {
                            self.rephase();
                        }
                    }
                }
                continue;
            }

            // No conflict.
            if (self.pickBranch()) |br| {
                try self.decide(br);
            } else {
                // Model
                if (self.opts.complete_model) {
                    for (self.assign) |*a| {
                        if (a.* == .undef) a.* = .false_;
                    }
                }
                if (!self.orig_cnf.checkModel(self.assign)) {
                    return error.ModelInvalid;
                }
                const model = try self.allocator.dupe(Value, self.assign);
                var proof_out: ?drat_mod.Proof = null;
                if (self.proof) |*pf| {
                    proof_out = pf.*;
                    self.proof = null;
                }
                return .{
                    .status = .sat,
                    .model = model,
                    .conflicts = self.conflict_count,
                    .decisions = self.decision_count,
                    .propagations = self.prop_count,
                    .learned = self.learned_count,
                    .reduced = self.reduced_count,
                    .proof = proof_out,
                };
            }
        }
    }

    fn finishUnsat(self: *Solver) !SolveResult {
        if (self.proof) |*pf| {
            try pf.addClause(&.{});
        }
        var proof_out: ?drat_mod.Proof = null;
        if (self.proof) |*pf| {
            const ok = try pf.verifyRup(self.allocator, &self.orig_cnf);
            if (!ok) return error.ProofInvalid;
            proof_out = pf.*;
            self.proof = null;
        }
        return .{
            .status = .unsat,
            .conflicts = self.conflict_count,
            .decisions = self.decision_count,
            .propagations = self.prop_count,
            .learned = self.learned_count,
            .reduced = self.reduced_count,
            .proof = proof_out,
        };
    }
};

test "assumption core is deletion-minimal" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    // (a ∨ b) ∧ (a ∨ c) — unsat under ~a,~b,~c; minimal cores include {~a,~b} or {~a,~c}
    cnf.ensureVars(3);
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    const c = Lit.positive(Var.fromIndex(2));
    try cnf.addClause(&.{ a, b });
    try cnf.addClause(&.{ a, c });
    var s = try Solver.init(std.testing.allocator, &cnf, .{});
    defer s.deinit();
    const ass = [_]Lit{ a.not(), b.not(), c.not() };
    const r = try s.solveAssumptions(&ass);
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    defer if (r.assumption_core) |core| std.testing.allocator.free(core);
    try std.testing.expect(r.status == .unsat);
    try std.testing.expect(r.assumption_core != null);
    try std.testing.expect(r.assumption_core.?.len >= 2);
    try std.testing.expect(r.assumption_core.?.len < 3 or r.assumption_core.?.len == 2);
    var core_lits: std.ArrayList(Lit) = .empty;
    defer core_lits.deinit(std.testing.allocator);
    for (r.assumption_core.?) |d| try core_lits.append(std.testing.allocator, Lit.fromDimacs(d));
    try std.testing.expect(try s.isDeletionMinimalCore(core_lits.items));
    // Two MUSes exist → not unique
    try std.testing.expect(!r.assumption_core_unique);
}

test "unique MUS when single minimal core" {
    // (a) ∧ (¬a ∨ b) ∧ (¬b) unsat under assumptions ~ forced... use units in formula
    // Formula: (x∨y) only, assumptions ~x,~y → unique MUS {~x,~y}
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(2);
    const x = Lit.positive(Var.fromIndex(0));
    const y = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ x, y });
    var s = try Solver.init(std.testing.allocator, &cnf, .{});
    defer s.deinit();
    const ass = [_]Lit{ x.not(), y.not() };
    const r = try s.solveAssumptions(&ass);
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    defer if (r.assumption_core) |core| std.testing.allocator.free(core);
    try std.testing.expect(r.status == .unsat);
    try std.testing.expect(r.assumption_core.?.len == 2);
    try std.testing.expect(r.assumption_core_unique);
}

test "multi-shot incremental assumptions" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ a, b });
    var s = try Solver.init(std.testing.allocator, &cnf, .{});
    defer s.deinit();
    const r1 = try s.solveAssumptions(&.{a});
    defer if (r1.model) |m| std.testing.allocator.free(m);
    defer if (r1.assumption_core) |c| std.testing.allocator.free(c);
    try std.testing.expect(r1.status == .sat);
    const r2 = try s.solveAssumptions(&.{ a.not(), b.not() });
    defer if (r2.assumption_core) |c| std.testing.allocator.free(c);
    try std.testing.expect(r2.status == .unsat);
    try std.testing.expect(r2.assumption_core != null);
    try std.testing.expect(r2.assumption_core.?.len >= 1);
    const r3 = try s.solveAssumptions(&.{b});
    defer if (r3.model) |m| std.testing.allocator.free(m);
    defer if (r3.assumption_core) |c| std.testing.allocator.free(c);
    try std.testing.expect(r3.status == .sat);
}

test "compact after deletes" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(6);
    var prng = std.Random.DefaultPrng.init(7);
    const rng = prng.random();
    var c: u32 = 0;
    while (c < 30) : (c += 1) {
        var cl: [3]Lit = undefined;
        var k: u32 = 0;
        while (k < 3) : (k += 1) {
            cl[k] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, 6)), rng.boolean());
        }
        try cnf.addClause(&cl);
    }
    var s = try Solver.init(std.testing.allocator, &cnf, .{
        .reduce_interval = 5,
        .reduce_keep_min = 2,
        .max_conflicts = 20_000,
    });
    defer s.deinit();
    const r = try s.solve();
    defer if (r.model) |m| std.testing.allocator.free(m);
    try s.compact();
    const r2 = try s.solve();
    defer if (r2.model) |m| std.testing.allocator.free(m);
    try std.testing.expect(r2.status == .sat or r2.status == .unsat);
}

pub fn solveCnf(allocator: std.mem.Allocator, cnf: *const Cnf, opts: SolverOptions) !SolveResult {
    var s = try Solver.init(allocator, cnf, opts);
    defer s.deinit();
    return try s.solve();
}

/// Solve under assumptions: each assumption is a temporary unit clause.
pub fn solveCnfAssumptions(
    allocator: std.mem.Allocator,
    cnf: *const Cnf,
    assumptions: []const Lit,
    opts: SolverOptions,
) !SolveResult {
    var work = Cnf.init(allocator);
    defer work.deinit();
    work.ensureVars(cnf.num_vars);
    for (0..cnf.numClauses()) |ci| {
        try work.addClause(cnf.clauseSlice(ClauseId.fromIndex(@intCast(ci))));
    }
    for (assumptions) |a| {
        try work.addClause(&.{a});
    }
    return try solveCnf(allocator, &work, opts);
}

test "assumptions force unsat" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ a, b });
    // assume ~a and ~b → unsat
    const r = try solveCnfAssumptions(std.testing.allocator, &cnf, &.{ a.not(), b.not() }, .{});
    try std.testing.expect(r.status == .unsat);
}

test "assumptions select model" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ a, b });
    const r = try solveCnfAssumptions(std.testing.allocator, &cnf, &.{a}, .{});
    defer if (r.model) |m| std.testing.allocator.free(m);
    try std.testing.expect(r.status == .sat);
    try std.testing.expect(r.model.?[0] == .true_);
}

pub const Error = error{
    ModelInvalid,
    ProofInvalid,
};

test "cdcl sat simple" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    const b = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{ a, b });
    try cnf.addClause(&.{ a.not(), b });
    try cnf.addClause(&.{b});
    const r = try solveCnf(std.testing.allocator, &cnf, .{});
    defer if (r.model) |m| std.testing.allocator.free(m);
    try std.testing.expect(r.status == .sat);
    try std.testing.expect(cnf.checkModel(r.model.?));
}

test "cdcl unsat with proof" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const a = Lit.positive(Var.fromIndex(0));
    try cnf.addClause(&.{a});
    try cnf.addClause(&.{a.not()});
    const r = try solveCnf(std.testing.allocator, &cnf, .{ .proof = true });
    try std.testing.expect(r.status == .unsat);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
}

test "cdcl pigeon unsat" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const p0 = Lit.positive(Var.fromIndex(0));
    const p1 = Lit.positive(Var.fromIndex(1));
    try cnf.addClause(&.{p0});
    try cnf.addClause(&.{p1});
    try cnf.addClause(&.{ p0.not(), p1.not() });
    const r = try solveCnf(std.testing.allocator, &cnf, .{ .proof = true });
    try std.testing.expect(r.status == .unsat);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
}

test "cdcl 3sat sat" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const x0 = Lit.positive(Var.fromIndex(0));
    const x1 = Lit.positive(Var.fromIndex(1));
    const x2 = Lit.positive(Var.fromIndex(2));
    try cnf.addClause(&.{ x0, x1, x2 });
    try cnf.addClause(&.{ x0.not(), x1 });
    try cnf.addClause(&.{ x1.not(), x2 });
    try cnf.addClause(&.{ x2.not(), x0, x1 });
    const r = try solveCnf(std.testing.allocator, &cnf, .{});
    defer std.testing.allocator.free(r.model.?);
    try std.testing.expect(r.status == .sat);
    try std.testing.expect(cnf.checkModel(r.model.?));
}

test "cdcl heap vsids and reduce path" {
    // Random-ish CNF large enough to learn + reduce.
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    const n: u32 = 12;
    cnf.ensureVars(n);
    var prng = std.Random.DefaultPrng.init(99);
    const rng = prng.random();
    var c: u32 = 0;
    while (c < 50) : (c += 1) {
        var cl: [3]Lit = undefined;
        var k: u32 = 0;
        while (k < 3) : (k += 1) {
            cl[k] = Lit.make(Var.fromIndex(rng.intRangeLessThan(u32, 0, n)), rng.boolean());
        }
        try cnf.addClause(&cl);
    }
    const r = try solveCnf(std.testing.allocator, &cnf, .{
        .reduce_interval = 10,
        .reduce_keep_min = 5,
        .max_conflicts = 50_000,
    });
    defer if (r.model) |m| std.testing.allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    try std.testing.expect(r.status == .sat or r.status == .unsat);
    if (r.status == .sat) {
        try std.testing.expect(cnf.checkModel(r.model.?));
    }
}
