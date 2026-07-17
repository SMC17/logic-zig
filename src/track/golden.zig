//! Golden corpus — built-in + file manifest (AIGER/CNF) + DRAT when available.

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const aiger = @import("../bridge/aiger.zig");
const solver_mod = @import("../sat/solver.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const kinduction = @import("../circuit/kinduction.zig");
const kliveness = @import("../circuit/kliveness.zig");
const justice = @import("../circuit/justice.zig");
const certificate = @import("../cert/certificate.zig");
const ctl = @import("../ctl/ctl.zig");
const portfolio = @import("../sat/portfolio.zig");
const agent_session = @import("../agent/session.zig");
const lit_mod = @import("../core/lit.zig");
const netlist_mod = @import("../circuit/netlist.zig");
const bv = @import("../smt/bv.zig");
const drat_external = @import("../sat/drat_external.zig");

const Lit = lit_mod.Lit;
const Var = lit_mod.Var;
const Netlist = netlist_mod.Netlist;

pub const GoldenResult = struct {
    total: u32 = 0,
    passed: u32 = 0,
    failed: u32 = 0,
    skipped: u32 = 0,
};

fn pass(res: *GoldenResult, ok: bool) void {
    res.total += 1;
    if (ok) res.passed += 1 else res.failed += 1;
}

fn skip(res: *GoldenResult) void {
    res.total += 1;
    res.skipped += 1;
}

/// Built-in golden cases (no files required).
pub fn runBuiltin(allocator: std.mem.Allocator) !GoldenResult {
    var res: GoldenResult = .{};

    // CNF unsat
    {
        var cnf = try dimacs.parse(allocator, "p cnf 1 2\n1 0\n-1 0\n");
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .unsat);
    }
    // CNF sat + portfolio
    {
        var cnf = try dimacs.parse(allocator, "p cnf 2 1\n1 2 0\n");
        defer cnf.deinit();
        const r = try portfolio.solvePortfolioOpts(allocator, &cnf, .{ .total_conflicts = 50_000 });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .sat and r.model_valid);
    }
    // portfolio unsat + optional proof
    {
        var cnf = try dimacs.parse(allocator, "p cnf 1 2\n1 0\n-1 0\n");
        defer cnf.deinit();
        var r = try portfolio.solvePortfolioOpts(allocator, &cnf, .{
            .total_conflicts = 100_000,
            .proof_on_unsat = true,
        });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .unsat);
    }
    // PDR stuck0 + invariant
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        var pr = try pdr.check(allocator, &nl, q, 12);
        defer pr.deinit(allocator);
        pass(&res, pr.status == .proven and pr.invariant_clauses != null);
    }
    // cert
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const inv = try certificate.fromPdrProven(allocator, &nl, q, 16);
        if (inv) |*i| {
            defer {
                var ii = i.*;
                ii.deinit();
            }
            pass(&res, try i.verify(allocator, &nl));
        } else pass(&res, false);
    }
    // BMC counter
    {
        var nl = Netlist.init(allocator);
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
        const br = try bmc.check(allocator, &nl, bad, 3);
        defer if (br.trace) |t| allocator.free(t);
        pass(&res, br.status == .violated);
    }
    // kind
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const kr = try kinduction.search(allocator, &nl, q, 4);
        defer if (kr.base.trace) |t| allocator.free(t);
        pass(&res, kr.status == .proven);
    }
    // klive
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const r = try kliveness.proveFiniteHits(allocator, &nl, q, 4, 16);
        pass(&res, r.status == .proven_infinite);
    }
    // fair multi one dead
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q0 = try nl.allocNetNamed("q0");
        const q1 = try nl.allocNetNamed("q1");
        const d0 = try nl.allocNetNamed("d0");
        const d1 = try nl.allocNetNamed("d1");
        try nl.addConst(d0, false);
        try nl.addGate(.not, &.{q1}, d1);
        try nl.addLatch(d0, q0, false);
        try nl.addLatch(d1, q1, false);
        const r = try kliveness.check(allocator, &nl, &.{ q0, q1 }, 4, 16, 0);
        pass(&res, r.status == .proven_infinite);
    }
    // fair multi dual lasso
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q0 = try nl.allocNetNamed("q0");
        const q1 = try nl.allocNetNamed("q1");
        const d0 = try nl.allocNetNamed("d0");
        const d1 = try nl.allocNetNamed("d1");
        try nl.addGate(.not, &.{q0}, d0);
        try nl.addGate(.xor, &.{ q1, q0 }, d1);
        try nl.addLatch(d0, q0, false);
        try nl.addLatch(d1, q1, false);
        const r = try kliveness.check(allocator, &nl, &.{ q0, q1 }, 1, 8, 8);
        pass(&res, r.status == .lasso_witness);
    }
    // CTL AG
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        const nq = try nl.allocNetNamed("nq");
        try nl.addConst(d, false);
        try nl.addGate(.not, &.{q}, nq);
        try nl.addLatch(d, q, false);
        const r = try ctl.checkAg(allocator, &nl, nq, 4);
        pass(&res, r.status == .holds);
    }
    // agent session
    {
        var s = agent_session.Session.init(allocator);
        defer s.deinit();
        s.ensureVars(2);
        const a = Lit.positive(Var.fromIndex(0));
        const b = Lit.positive(Var.fromIndex(1));
        try s.addClause(&.{ a, b });
        const r = try s.query(&.{ a.not(), b.not() });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.core) |c| allocator.free(c);
        pass(&res, r.status == .unsat and r.core_unique);
    }
    // BV
    {
        var w = bv.BvWorld.init(allocator);
        defer w.deinit();
        const x = try w.mkConst(4, 3);
        const y = try w.mkConst(4, 5);
        const s = try w.mkAdd(x, y);
        const eight = try w.mkConst(4, 8);
        try w.assertEq(s, eight);
        pass(&res, (try w.checkSat()) == .sat);
    }
    // RUP cert
    {
        var cnf = @import("../sat/cnf.zig").Cnf.init(allocator);
        defer cnf.deinit();
        cnf.ensureVars(1);
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(0))});
        try cnf.addClause(&.{Lit.negative(Var.fromIndex(0))});
        const c = try certificate.unsatWithProof(allocator, &cnf);
        pass(&res, c.unsat and c.proof_clauses >= 1);
    }
    // Internal DRAT self-check (always)
    {
        var cnf = try dimacs.parse(allocator, "p cnf 1 2\n1 0\n-1 0\n");
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{ .proof = true });
        defer if (r.model) |m| allocator.free(m);
        if (r.proof) |*p| {
            defer {
                var pp = p.*;
                pp.deinit();
            }
            pass(&res, r.status == .unsat and try p.verifyRup(allocator, &cnf));
        } else pass(&res, false);
    }
    // fair multi three-signal
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const a = try nl.allocNetNamed("a");
        const b = try nl.allocNetNamed("b");
        const c = try nl.allocNetNamed("c");
        const da = try nl.allocNetNamed("da");
        const db = try nl.allocNetNamed("db");
        const dc = try nl.allocNetNamed("dc");
        try nl.addGate(.not, &.{a}, da);
        try nl.addGate(.not, &.{b}, db);
        try nl.addConst(dc, false);
        try nl.addLatch(da, a, false);
        try nl.addLatch(db, b, false);
        try nl.addLatch(dc, c, false);
        const r = try kliveness.proveFairMulti(allocator, &nl, &.{ a, b, c }, 5, 16);
        pass(&res, r.status == .proven_infinite);
    }

    return res;
}

/// File-based manifest cases (JSONL lines). Soft-skip missing files.
pub fn runManifest(allocator: std.mem.Allocator, io: std.Io, manifest_path: []const u8) !GoldenResult {
    var res: GoldenResult = .{};
    const body = std.Io.Dir.cwd().readFileAlloc(io, manifest_path, allocator, .limited(1 << 20)) catch {
        skip(&res);
        return res;
    };
    defer allocator.free(body);

    var lines = std.mem.splitScalar(u8, body, '\n');
    while (lines.next()) |raw| {
        const line = std.mem.trim(u8, raw, " \t\r");
        if (line.len == 0 or line[0] == '#') continue;
        const path = extractJsonString(line, "path") orelse continue;
        const kind = extractJsonString(line, "kind") orelse continue;
        const expect = extractJsonString(line, "expect") orelse continue;

        const src = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(16 << 20)) catch {
            skip(&res);
            continue;
        };
        defer allocator.free(src);

        if (std.mem.eql(u8, kind, "cnf")) {
            var cnf = dimacs.parse(allocator, src) catch {
                pass(&res, false);
                continue;
            };
            defer cnf.deinit();
            const r = try solver_mod.solveCnf(allocator, &cnf, .{});
            defer if (r.model) |m| allocator.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            const ok = (std.mem.eql(u8, expect, "unsat") and r.status == .unsat) or
                (std.mem.eql(u8, expect, "sat") and r.status == .sat);
            pass(&res, ok);
        } else if (std.mem.eql(u8, kind, "aiger-parse")) {
            var nl = aiger.parse(allocator, src) catch {
                pass(&res, false);
                continue;
            };
            defer nl.deinit();
            pass(&res, std.mem.eql(u8, expect, "ok") and nl.num_nets > 0);
        } else if (std.mem.eql(u8, kind, "aiger-safe")) {
            var nl = aiger.parse(allocator, src) catch {
                pass(&res, false);
                continue;
            };
            defer nl.deinit();
            const props = nl.badProps();
            if (props.len == 0) {
                pass(&res, std.mem.eql(u8, expect, "safe"));
                continue;
            }
            var pr = try pdr.check(allocator, &nl, props[0], 16);
            defer pr.deinit(allocator);
            if (pr.status == .proven) {
                pass(&res, std.mem.eql(u8, expect, "safe"));
            } else if (pr.status == .violated) {
                pass(&res, std.mem.eql(u8, expect, "unsafe"));
            } else {
                const br = try bmc.check(allocator, &nl, props[0], 8);
                defer if (br.trace) |t| allocator.free(t);
                if (br.status == .violated) {
                    pass(&res, std.mem.eql(u8, expect, "unsafe"));
                } else if (std.mem.eql(u8, expect, "unknown")) {
                    pass(&res, true);
                } else {
                    // kind fallback for stuck0-style
                    const kr = try kinduction.search(allocator, &nl, props[0], 6);
                    defer if (kr.base.trace) |t| allocator.free(t);
                    pass(&res, (kr.status == .proven and std.mem.eql(u8, expect, "safe")) or
                        (kr.status == .violated and std.mem.eql(u8, expect, "unsafe")));
                }
            }
        } else if (std.mem.eql(u8, kind, "aiger-lasso")) {
            var nl = aiger.parse(allocator, src) catch {
                pass(&res, false);
                continue;
            };
            defer nl.deinit();
            const j = if (nl.justice.items.len > 0) nl.justice.items else nl.outputs.items;
            const r = try justice.checkLasso(allocator, &nl, j, nl.fairness.items, 6);
            defer if (r.trace) |t| allocator.free(t);
            pass(&res, std.mem.eql(u8, expect, "witness") and r.status == .witness);
        } else if (std.mem.eql(u8, kind, "aiger-klive")) {
            var nl = aiger.parse(allocator, src) catch {
                pass(&res, false);
                continue;
            };
            defer nl.deinit();
            const r = try kliveness.checkNetlist(allocator, &nl, 4, 16, 0);
            pass(&res, std.mem.eql(u8, expect, "proven_infinite") and r.status == .proven_infinite);
        } else {
            skip(&res);
        }
    }
    return res;
}

/// External DRAT-trim on unit unsat when checker present.
pub fn runDratExternal(allocator: std.mem.Allocator, io: std.Io) !GoldenResult {
    var res: GoldenResult = .{};
    const checker = try drat_external.findDratTrim(allocator);
    if (checker == null) {
        skip(&res);
        return res;
    }
    defer allocator.free(checker.?);

    var cnf = try dimacs.parse(allocator, "p cnf 1 2\n1 0\n-1 0\n");
    defer cnf.deinit();
    const r = try drat_external.solveAndCheckExternal(allocator, io, &cnf);
    // verified is ideal; internal_error/unavailable soft-skip under sandbox
    if (r.check == .verified) {
        pass(&res, r.status == .unsat);
    } else if (r.check == .failed) {
        pass(&res, false);
    } else {
        skip(&res);
    }
    return res;
}

fn extractJsonString(line: []const u8, key: []const u8) ?[]const u8 {
    // naive "key":"value"
    var buf: [64]u8 = undefined;
    const pat = std.fmt.bufPrint(&buf, "\"{s}\":\"", .{key}) catch return null;
    const start = std.mem.indexOf(u8, line, pat) orelse return null;
    const v0 = start + pat.len;
    const v1 = std.mem.indexOfScalarPos(u8, line, v0, '"') orelse return null;
    return line[v0..v1];
}

pub fn runAll(allocator: std.mem.Allocator, io: std.Io) !GoldenResult {
    var res = try runBuiltin(allocator);
    const m = try runManifest(allocator, io, "corpus/golden/manifest.jsonl");
    res.total += m.total;
    res.passed += m.passed;
    res.failed += m.failed;
    res.skipped += m.skipped;
    const d = try runDratExternal(allocator, io);
    res.total += d.total;
    res.passed += d.passed;
    res.failed += d.failed;
    res.skipped += d.skipped;
    return res;
}

pub fn printResult(r: *const GoldenResult) void {
    std.debug.print("golden: {d}/{d} passed, {d} failed, {d} skipped\n", .{
        r.passed,
        r.total,
        r.failed,
        r.skipped,
    });
}

test "golden builtin all pass" {
    const r = try runBuiltin(std.testing.allocator);
    try std.testing.expect(r.failed == 0);
    try std.testing.expect(r.passed == r.total);
    try std.testing.expect(r.total >= 14);
}
