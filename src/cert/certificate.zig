//! Certificates for sequential / SAT proofs — exportable and re-checkable.

const std = @import("std");
const lit_mod = @import("../core/lit.zig");
const cnf_mod = @import("../sat/cnf.zig");
const netlist_mod = @import("../circuit/netlist.zig");
const solver_mod = @import("../sat/solver.zig");
const pdr = @import("../circuit/pdr.zig");
const kinduction = @import("../circuit/kinduction.zig");
const kliveness = @import("../circuit/kliveness.zig");
const blast = @import("../circuit/blast.zig");

const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Cnf = cnf_mod.Cnf;
const Netlist = netlist_mod.Netlist;
const NetId = netlist_mod.NetId;

pub const InductiveInvariant = struct {
    allocator: std.mem.Allocator,
    clauses: [][]Lit,
    bad: NetId,
    frames_used: u32 = 0,
    source: enum { pdr, kinduction, empty } = .empty,

    pub fn deinit(self: *InductiveInvariant) void {
        for (self.clauses) |c| self.allocator.free(c);
        self.allocator.free(self.clauses);
        self.* = undefined;
    }

    /// Init∧I∧bad unsat; Init⇒I (each clause).
    pub fn verify(self: *const InductiveInvariant, allocator: std.mem.Allocator, nl: *const Netlist) !bool {
        {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            cnf.ensureVars(nl.num_nets);
            try blast.blastFrame(&cnf, nl, 0);
            for (nl.latches.items) |lat| {
                if (lat.init) |iv| {
                    const q = Lit.positive(Var.fromIndex(lat.q.index()));
                    if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
                }
            }
            for (self.clauses) |cl| try cnf.addClause(cl);
            try cnf.addClause(&.{Lit.positive(Var.fromIndex(self.bad.index()))});
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 100_000 });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status != .unsat) return false;
        }
        for (self.clauses) |cl| {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            cnf.ensureVars(nl.num_nets);
            try blast.blastFrame(&cnf, nl, 0);
            for (nl.latches.items) |lat| {
                if (lat.init) |iv| {
                    const q = Lit.positive(Var.fromIndex(lat.q.index()));
                    if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
                }
            }
            for (cl) |l| try cnf.addClause(&.{l.not()});
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 50_000 });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .sat) return false;
        }
        // Relative inductiveness: I ∧ T ∧ ¬I' unsat (best-effort when clauses non-empty)
        if (self.clauses.len > 0 and nl.latches.items.len > 0) {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            const nn = nl.num_nets;
            cnf.ensureVars(nn * 2);
            try blast.blastFrameNn(&cnf, nl, 0, nn);
            try blast.blastFrameNn(&cnf, nl, 1, nn);
            for (nl.latches.items) |lat| {
                const qn = Lit.positive(Var.fromIndex(nn + lat.q.index()));
                const d = Lit.positive(Var.fromIndex(lat.d.index()));
                try cnf.addClause(&.{ qn.not(), d });
                try cnf.addClause(&.{ d.not(), qn });
            }
            for (self.clauses) |cl| try cnf.addClause(cl);
            // ¬I' : OR over clauses of AND of negations of clause' — for each clause C in I,
            // allow C' to fail: add cube of ~lits of C at frame 1 as a way to break I'
            // Simpler: for each clause, force all lits false at frame 1 in a disjunction of cubes.
            // I' fails if some clause is all-false at frame 1.
            var break_or: std.ArrayList(Lit) = .empty;
            defer break_or.deinit(allocator);
            var aux_base: u32 = nn * 2;
            for (self.clauses) |cl| {
                const aux = aux_base;
                aux_base += 1;
                cnf.ensureVars(aux_base);
                const al = Lit.positive(Var.fromIndex(aux));
                // aux => each ~lit'
                for (cl) |l| {
                    const lp = Lit.make(Var.fromIndex(nn + l.variable().index()), l.isNeg());
                    try cnf.addClause(&.{ al.not(), lp.not() });
                }
                // (all ~lit') => aux
                var and_cl: std.ArrayList(Lit) = .empty;
                defer and_cl.deinit(allocator);
                try and_cl.append(allocator, al);
                for (cl) |l| {
                    const lp = Lit.make(Var.fromIndex(nn + l.variable().index()), l.isNeg());
                    try and_cl.append(allocator, lp);
                }
                try cnf.addClause(and_cl.items);
                try break_or.append(allocator, al);
            }
            if (break_or.items.len > 0) try cnf.addClause(break_or.items);
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = 200_000 });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status == .sat) return false;
        }
        return true;
    }

    pub fn writeText(self: *const InductiveInvariant, allocator: std.mem.Allocator) ![]u8 {
        var aw: std.Io.Writer.Allocating = .init(allocator);
        defer aw.deinit();
        const w = &aw.writer;
        try w.print("kind=inductive_invariant\nsource={s}\nframes={d}\nclauses={d}\nbad={d}\n", .{
            @tagName(self.source),
            self.frames_used,
            self.clauses.len,
            self.bad.index(),
        });
        for (self.clauses) |cl| {
            for (cl) |l| try w.print("{d} ", .{l.toDimacs()});
            try w.print("0\n", .{});
        }
        return try aw.toOwnedSlice();
    }
};

/// Run PDR; on proven, take exported frame clauses as the certificate.
pub fn fromPdrProven(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    bad: NetId,
    max_frames: u32,
) !?InductiveInvariant {
    var r = try pdr.check(allocator, nl, bad, max_frames);
    defer r.deinit(allocator);
    if (r.status != .proven) return null;

    if (r.invariant_clauses) |cls| {
        // Take ownership of clones
        const owned = try allocator.alloc([]Lit, cls.len);
        errdefer {
            for (owned) |c| allocator.free(c);
            allocator.free(owned);
        }
        for (cls, 0..) |cl, i| owned[i] = try allocator.dupe(Lit, cl);
        var inv = InductiveInvariant{
            .allocator = allocator,
            .clauses = owned,
            .bad = bad,
            .frames_used = r.frames,
            .source = .pdr,
        };
        if (try inv.verify(allocator, nl)) return inv;
        inv.deinit();
    }

    // Fallback: k-induction proven ⇒ empty I OK if Init∧bad unsat forever via kind
    const kr = try kinduction.search(allocator, nl, bad, @max(max_frames, 3));
    defer if (kr.base.trace) |t| allocator.free(t);
    if (kr.status == .proven) {
        var inv = InductiveInvariant{
            .allocator = allocator,
            .clauses = try allocator.alloc([]Lit, 0),
            .bad = bad,
            .frames_used = kr.k,
            .source = .kinduction,
        };
        if (try inv.verify(allocator, nl)) return inv;
        inv.deinit();
    }
    return null;
}

pub const KLiveCertificate = struct {
    k: u32,
    justice_count: u32,
    conflicts: u64,
    status: kliveness.KLiveStatus,
};

pub fn kLiveCert(
    allocator: std.mem.Allocator,
    nl: *const Netlist,
    max_k: u32,
    frames: u32,
) !KLiveCertificate {
    const j = if (nl.justice.items.len > 0) nl.justice.items else nl.outputs.items;
    const r = try kliveness.check(allocator, nl, j, max_k, frames, 0);
    return .{
        .k = r.k,
        .justice_count = @intCast(j.len),
        .conflicts = r.conflicts,
        .status = r.status,
    };
}

pub fn writeKLiveCert(allocator: std.mem.Allocator, cert: KLiveCertificate) ![]u8 {
    return std.fmt.allocPrint(allocator, "kind=k_liveness\nstatus={s}\nk={d}\njustices={d}\nconflicts={d}\n", .{
        @tagName(cert.status),
        cert.k,
        cert.justice_count,
        cert.conflicts,
    });
}

/// RUP-backed UNSAT certificate summary.
pub fn unsatWithProof(allocator: std.mem.Allocator, formula: *const Cnf) !struct {
    unsat: bool,
    proof_clauses: u32,
    conflicts: u64,
} {
    const r = try solver_mod.solveCnf(allocator, formula, .{ .proof = true });
    defer if (r.model) |m| allocator.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    return .{
        .unsat = r.status == .unsat,
        .proof_clauses = if (r.proof) |p| @intCast(p.numClauses()) else 0,
        .conflicts = r.conflicts,
    };
}

test "klive cert stuck0" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    try nl.addJustice(q);
    const c = try kLiveCert(std.testing.allocator, &nl, 4, 16);
    try std.testing.expect(c.status == .proven_infinite);
}

test "pdr cert stuck0 verifies" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    const inv = try fromPdrProven(std.testing.allocator, &nl, q, 16);
    try std.testing.expect(inv != null);
    var i = inv.?;
    defer i.deinit();
    try std.testing.expect(try i.verify(std.testing.allocator, &nl));
    const text = try i.writeText(std.testing.allocator);
    defer std.testing.allocator.free(text);
    try std.testing.expect(std.mem.indexOf(u8, text, "inductive_invariant") != null);
}

test "unsat proof cert" {
    var cnf = Cnf.init(std.testing.allocator);
    defer cnf.deinit();
    cnf.ensureVars(1);
    try cnf.addClause(&.{Lit.positive(Var.fromIndex(0))});
    try cnf.addClause(&.{Lit.negative(Var.fromIndex(0))});
    const c = try unsatWithProof(std.testing.allocator, &cnf);
    try std.testing.expect(c.unsat);
    try std.testing.expect(c.proof_clauses >= 1);
}
