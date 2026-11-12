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
    pub const Source = enum { pdr, kinduction, supplied, empty };
    allocator: std.mem.Allocator,
    clauses: [][]Lit,
    bad: NetId,
    frames_used: u32 = 0,
    source: Source = .empty,

    pub fn deinit(self: *InductiveInvariant) void {
        for (self.clauses) |c| self.allocator.free(c);
        self.allocator.free(self.clauses);
        self.* = undefined;
    }

    pub const VerifyOptions = struct {
        max_conflicts: u64 = 200_000,
    };

    /// I excludes bad states, Init implies I, and I is preserved by transitions.
    pub fn verify(self: *const InductiveInvariant, allocator: std.mem.Allocator, nl: *const Netlist) !bool {
        return self.verifyWithOptions(allocator, nl, .{});
    }

    pub fn verifyWithOptions(self: *const InductiveInvariant, allocator: std.mem.Allocator, nl: *const Netlist, opts: VerifyOptions) !bool {
        if (self.bad.index() >= nl.num_nets) return false;
        for (self.clauses) |cl| {
            for (cl) |l| if (l.variable().index() >= nl.num_nets) return false;
        }
        {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            cnf.ensureVars(nl.num_nets);
            try blast.blastFrame(&cnf, nl, 0);
            // Exclusion must hold in every state admitted by I, not only Init.
            for (nl.constraints.items) |c| try cnf.addClause(&.{Lit.positive(Var.fromIndex(c.index()))});
            for (self.clauses) |cl| try cnf.addClause(cl);
            try cnf.addClause(&.{Lit.positive(Var.fromIndex(self.bad.index()))});
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = opts.max_conflicts });
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
            for (nl.constraints.items) |c| try cnf.addClause(&.{Lit.positive(Var.fromIndex(c.index()))});
            for (nl.latches.items) |lat| {
                if (lat.init) |iv| {
                    const q = Lit.positive(Var.fromIndex(lat.q.index()));
                    if (iv) try cnf.addClause(&.{q}) else try cnf.addClause(&.{q.not()});
                }
            }
            for (cl) |l| try cnf.addClause(&.{l.not()});
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = opts.max_conflicts });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status != .unsat) return false;
        }
        // Relative inductiveness: I ∧ T ∧ ¬I' must be UNSAT. Combinational
        // systems still need this check when their primary inputs can change.
        if (self.clauses.len > 0) {
            var cnf = Cnf.init(allocator);
            defer cnf.deinit();
            const nn = nl.num_nets;
            cnf.ensureVars(nn * 2);
            try blast.blastFrameNn(&cnf, nl, 0, nn);
            try blast.blastFrameNn(&cnf, nl, 1, nn);
            for (nl.constraints.items) |c| {
                try cnf.addClause(&.{Lit.positive(Var.fromIndex(c.index()))});
                try cnf.addClause(&.{Lit.positive(Var.fromIndex(nn + c.index()))});
            }
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
            const r = try solver_mod.solveCnf(allocator, &cnf, .{ .max_conflicts = opts.max_conflicts });
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            if (r.status != .unsat) return false;
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

    /// Read the exact exported format. Literal zero terminates each clause;
    /// extra tokens, missing clauses and malformed headers are refused.
    pub fn parseText(allocator: std.mem.Allocator, text: []const u8) !InductiveInvariant {
        var lines = std.mem.tokenizeAny(u8, text, "\r\n");
        if (!std.mem.eql(u8, lines.next() orelse return error.InvalidCertificate, "kind=inductive_invariant")) return error.InvalidCertificate;
        const source = std.meta.stringToEnum(Source, try header(&lines, "source=")) orelse return error.InvalidCertificate;
        const frames = std.fmt.parseInt(u32, try header(&lines, "frames="), 10) catch return error.InvalidCertificate;
        const count = std.fmt.parseInt(u32, try header(&lines, "clauses="), 10) catch return error.InvalidCertificate;
        const bad = std.fmt.parseInt(u32, try header(&lines, "bad="), 10) catch return error.InvalidCertificate;
        var clauses: std.ArrayList([]Lit) = .empty;
        errdefer {
            for (clauses.items) |clause| allocator.free(clause);
            clauses.deinit(allocator);
        }
        for (0..count) |_| {
            const line = lines.next() orelse return error.InvalidCertificate;
            var tokens = std.mem.tokenizeAny(u8, line, " \t");
            var literals: std.ArrayList(Lit) = .empty;
            defer literals.deinit(allocator);
            var terminated = false;
            while (tokens.next()) |token| {
                const dimension = std.fmt.parseInt(i32, token, 10) catch return error.InvalidCertificate;
                if (dimension == 0) {
                    terminated = true;
                    if (tokens.next() != null) return error.InvalidCertificate;
                    break;
                }
                if (dimension == std.math.minInt(i32)) return error.InvalidCertificate;
                try literals.append(allocator, Lit.fromDimacs(dimension));
            }
            if (!terminated) return error.InvalidCertificate;
            const owned = try literals.toOwnedSlice(allocator);
            errdefer allocator.free(owned);
            try clauses.append(allocator, owned);
        }
        if (lines.next() != null) return error.InvalidCertificate;
        return .{
            .allocator = allocator,
            .clauses = try clauses.toOwnedSlice(allocator),
            .bad = NetId.fromIndex(bad),
            .frames_used = frames,
            .source = source,
        };
    }

    fn header(lines: *std.mem.TokenIterator(u8, .any), prefix: []const u8) ![]const u8 {
        const line = lines.next() orelse return error.InvalidCertificate;
        if (!std.mem.startsWith(u8, line, prefix)) return error.InvalidCertificate;
        return line[prefix.len..];
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

test "initial safety does not make an empty invariant a safety certificate" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, true);
    try nl.addLatch(d, q, false);
    var candidate = InductiveInvariant{
        .allocator = std.testing.allocator,
        .clauses = try std.testing.allocator.alloc([]Lit, 0),
        .bad = q,
    };
    defer candidate.deinit();
    try std.testing.expect(!try candidate.verify(std.testing.allocator, &nl));
}

test "invariant verification refuses unknown implication and invalid variables" {
    var nl = Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const bad = try nl.allocNetNamed("bad");
    try nl.addConst(bad, false);
    try nl.addLatch(q, q, false);
    const clauses = try std.testing.allocator.alloc([]Lit, 1);
    clauses[0] = try std.testing.allocator.dupe(Lit, &.{Lit.positive(Var.fromIndex(q.index()))});
    var candidate = InductiveInvariant{
        .allocator = std.testing.allocator,
        .clauses = clauses,
        .bad = bad,
    };
    defer candidate.deinit();
    // Safety exclusion is trivially UNSAT, but Init => q is false. With a zero
    // search budget its satisfiable counterexample is UNKNOWN, never evidence.
    try std.testing.expect(!try candidate.verifyWithOptions(std.testing.allocator, &nl, .{ .max_conflicts = 0 }));
    clauses[0][0] = Lit.positive(Var.fromIndex(nl.num_nets));
    try std.testing.expect(!try candidate.verify(std.testing.allocator, &nl));
}

test "invariant text round-trips and rejects truncated or trailing evidence" {
    const text = "kind=inductive_invariant\nsource=pdr\nframes=2\nclauses=1\nbad=0\n-1 0\n";
    var candidate = try InductiveInvariant.parseText(std.testing.allocator, text);
    defer candidate.deinit();
    const written = try candidate.writeText(std.testing.allocator);
    defer std.testing.allocator.free(written);
    try std.testing.expectEqualStrings(text, written);
    try std.testing.expectError(error.InvalidCertificate, InductiveInvariant.parseText(std.testing.allocator, text ++ "0\n"));
    try std.testing.expectError(error.InvalidCertificate, InductiveInvariant.parseText(std.testing.allocator, "kind=inductive_invariant\nsource=pdr\nframes=2\nclauses=1\nbad=0\n-1\n"));
    try std.testing.expectError(error.InvalidCertificate, InductiveInvariant.parseText(std.testing.allocator, "kind=inductive_invariant\nsource=pdr\nframes=2\nclauses=1\nbad=0\n-2147483648 0\n"));
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
