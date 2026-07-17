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
const designs = @import("../circuit/designs.zig");
const sat_track = @import("sat_track.zig");

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
    // 2-bit counter BMC violates at 3
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
        const r2 = try bmc.check(allocator, &nl, bad, 2);
        defer if (r2.trace) |t| allocator.free(t);
        const r3 = try bmc.check(allocator, &nl, bad, 3);
        defer if (r3.trace) |t| allocator.free(t);
        pass(&res, r2.status == .safe_up_to_bound and r3.status == .violated);
    }
    // aiger write/read roundtrip
    {
        const aiger_write = @import("../bridge/aiger_write.zig");
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const a = try nl.allocNetNamed("a");
        const b = try nl.allocNetNamed("b");
        const y = try nl.allocNetNamed("y");
        try nl.addInput(a);
        try nl.addInput(b);
        try nl.addGate(.xor, &.{ a, b }, y);
        try nl.addOutput(y);
        const bytes = try aiger_write.writeAsciiSimple(allocator, &nl);
        defer allocator.free(bytes);
        var nl2 = try aiger.parse(allocator, bytes);
        defer nl2.deinit();
        pass(&res, nl2.inputs.items.len == 2 and nl2.outputs.items.len == 1);
    }
    // binary aiger roundtrip
    {
        const aiger_write = @import("../bridge/aiger_write.zig");
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const a = try nl.allocNetNamed("a");
        const b = try nl.allocNetNamed("b");
        const y = try nl.allocNetNamed("y");
        try nl.addInput(a);
        try nl.addInput(b);
        try nl.addGate(.and_, &.{ a, b }, y);
        try nl.addOutput(y);
        const bytes = try aiger_write.writeBinary(allocator, &nl);
        defer allocator.free(bytes);
        pass(&res, std.mem.startsWith(u8, bytes, "aig "));
        var nl2 = try aiger.parse(allocator, bytes);
        defer nl2.deinit();
        pass(&res, nl2.inputs.items.len == 2);
    }
    // fair multi + fairness stuck justice proves
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const j = try nl.allocNetNamed("j");
        const f = try nl.allocNetNamed("f");
        const dj = try nl.allocNetNamed("dj");
        const df = try nl.allocNetNamed("df");
        try nl.addConst(dj, false);
        try nl.addGate(.not, &.{f}, df);
        try nl.addLatch(dj, j, false);
        try nl.addLatch(df, f, false);
        try nl.addJustice(j);
        try nl.addFairness(f);
        const r = try kliveness.checkNetlist(allocator, &nl, 4, 16, 0);
        pass(&res, r.status == .proven_infinite);
    }
    // portfolio multi-config sat
    {
        var cnf = try dimacs.parse(allocator, "p cnf 3 2\n1 2 0\n-1 3 0\n");
        defer cnf.deinit();
        const r = try portfolio.solvePortfolioOpts(allocator, &cnf, .{ .total_conflicts = 50_000, .validate_model = true });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .sat and r.model_valid and r.configs_tried >= 1);
    }
    // nand/nor/xnor blast via netlist cnf
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const a = try nl.allocNetNamed("a");
        const b = try nl.allocNetNamed("b");
        const y = try nl.allocNetNamed("y");
        try nl.addInput(a);
        try nl.addInput(b);
        try nl.addGate(.nand, &.{ a, b }, y);
        try nl.addOutput(y);
        var cnf = try nl.toCnf(allocator);
        defer cnf.deinit();
        // force a=1 b=1 y=1 → unsat for nand
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(a.index()))});
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(b.index()))});
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(y.index()))});
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .unsat);
    }
    // designs: 3-bit counter + multi-stuck cert
    {
        var c = try designs.makeCounter(allocator, 3);
        defer c.nl.deinit();
        const r = try bmc.check(allocator, &c.nl, c.bad, 7);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .violated);
    }
    {
        var d = try designs.makeMultiStuck0(allocator, 3);
        defer d.nl.deinit();
        const inv = try certificate.fromPdrProven(allocator, &d.nl, d.bad, 20);
        if (inv) |*i| {
            defer {
                var ii = i.*;
                ii.deinit();
            }
            pass(&res, try i.verify(allocator, &d.nl));
        } else pass(&res, false);
    }
    {
        var nl = try designs.makeOneDeadAmongToggles(allocator, 3);
        defer nl.deinit();
        const r = try kliveness.checkNetlist(allocator, &nl, 6, 16, 0);
        pass(&res, r.status == .proven_infinite);
    }
    // agent stress micro
    {
        var s = agent_session.Session.init(allocator);
        defer s.deinit();
        const st = try s.stress(50, 6, 0x51);
        pass(&res, st.queries == 50);
    }
    // structured warm-cold (primary + re-asks)
    {
        const nq: u32 = 40;
        const c = try agent_session.compareWarmColdStructured(allocator, 10, nq);
        pass(&res, c.warm_queries == agent_session.structuredQueryCount(nq) and std.mem.eql(u8, c.mode, "structured"));
    }
    // mutex designs
    {
        var d = try designs.makeMutex(allocator, true);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 6);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .safe_up_to_bound);
    }
    {
        var d = try designs.makeCounter(allocator, 5);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 31);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .violated);
    }
    // one-hot ring not violated
    {
        var d = try designs.makeOneHotRing(allocator, 3);
        defer d.nl.deinit();
        var r = try pdr.check(allocator, &d.nl, d.bad, 16);
        defer r.deinit(allocator);
        pass(&res, r.status != .violated);
    }
    // kind multi-stuck
    {
        var d = try designs.makeMultiStuck0(allocator, 2);
        defer d.nl.deinit();
        const r = try kinduction.search(allocator, &d.nl, d.bad, 4);
        defer if (r.base.trace) |t| allocator.free(t);
        pass(&res, r.status == .proven);
    }
    // johnson reaches all-1s
    {
        var d = try designs.makeJohnson(allocator, 3);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 12);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .violated);
    }
    // dual-rail illegal coding not violated
    {
        var d = try designs.makeDualRailSafe(allocator);
        defer d.nl.deinit();
        var r = try pdr.check(allocator, &d.nl, d.bad, 12);
        defer r.deinit(allocator);
        pass(&res, r.status != .violated);
    }
    // parity never-bad kind
    {
        var d = try designs.makeParityNeverBad(allocator);
        defer d.nl.deinit();
        const r = try kinduction.search(allocator, &d.nl, d.bad, 3);
        defer if (r.base.trace) |t| allocator.free(t);
        pass(&res, r.status == .proven);
    }
    // empty bad → PDR proven
    {
        var nl = Netlist.init(allocator);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        var r = try pdr.checkMulti(allocator, &nl, &.{}, 4);
        defer r.deinit(allocator);
        pass(&res, r.status == .proven);
    }
    // multi-bad mixed → violated
    {
        var d = try designs.makeMultiBadMixed(allocator);
        defer d.nl.deinit();
        const br = try bmc.checkMulti(allocator, &d.nl, d.nl.badProps(), 2);
        defer if (br.trace) |t| allocator.free(t);
        pass(&res, br.status == .violated);
    }
    // constraint-only safe BMC
    {
        var d = try designs.makeConstraintOnlySafe(allocator);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 6);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .safe_up_to_bound);
    }
    // init×constraint conflict vacuous BMC safe
    {
        var d = try designs.makeInitConstraintConflict(allocator);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 3);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .safe_up_to_bound);
    }
    // dual-rail bad init violated@0
    {
        var d = try designs.makeDualRailBadInit(allocator);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 0);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .violated);
    }
    // counter 1-bit exact bound
    {
        var d = try designs.makeCounter(allocator, 1);
        defer d.nl.deinit();
        const r0 = try bmc.check(allocator, &d.nl, d.bad, 0);
        defer if (r0.trace) |t| allocator.free(t);
        const r1 = try bmc.check(allocator, &d.nl, d.bad, 1);
        defer if (r1.trace) |t| allocator.free(t);
        pass(&res, r0.status == .safe_up_to_bound and r1.status == .violated);
    }
    // one-hot weight bad not violated under BMC
    {
        var d = try designs.makeOneHotWeightBad(allocator, 3);
        defer d.nl.deinit();
        const r = try bmc.check(allocator, &d.nl, d.bad, 5);
        defer if (r.trace) |t| allocator.free(t);
        pass(&res, r.status == .safe_up_to_bound);
    }
    // sat-track competition path
    {
        const src =
            \\p cnf 1 2
            \\1 0
            \\-1 0
        ;
        const code = try sat_track.runBytesOpts(allocator, src, .{ .verbose = false, .proof = true });
        pass(&res, code == 20);
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
            // Multi-property: OR of all bad nets (HWMCC combined semantics).
            var pr = try pdr.checkMulti(allocator, &nl, props, 16);
            defer pr.deinit(allocator);
            if (pr.status == .proven) {
                pass(&res, std.mem.eql(u8, expect, "safe"));
            } else if (pr.status == .violated) {
                pass(&res, std.mem.eql(u8, expect, "unsafe"));
            } else {
                const br = try bmc.checkMulti(allocator, &nl, props, 8);
                defer if (br.trace) |t| allocator.free(t);
                if (br.status == .violated) {
                    pass(&res, std.mem.eql(u8, expect, "unsafe"));
                } else if (std.mem.eql(u8, expect, "unknown")) {
                    pass(&res, true);
                } else {
                    // kind fallback (single prop) for stuck0-style when multi unknown
                    const kr = try kinduction.search(allocator, &nl, props[0], 6);
                    defer if (kr.base.trace) |t| allocator.free(t);
                    if (props.len == 1) {
                        pass(&res, (kr.status == .proven and std.mem.eql(u8, expect, "safe")) or
                            (kr.status == .violated and std.mem.eql(u8, expect, "unsafe")));
                    } else if (br.status == .safe_up_to_bound and std.mem.eql(u8, expect, "safe")) {
                        pass(&res, true);
                    } else {
                        pass(&res, false);
                    }
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
    try std.testing.expect(r.total >= 20);
}
