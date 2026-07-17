//! Golden corpus — correctness vertical across SAT / MC / liveness / cert / agent.

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const aiger = @import("../bridge/aiger.zig");
const solver_mod = @import("../sat/solver.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const kinduction = @import("../circuit/kinduction.zig");
const kliveness = @import("../circuit/kliveness.zig");
const certificate = @import("../cert/certificate.zig");
const ctl = @import("../ctl/ctl.zig");
const portfolio = @import("../sat/portfolio.zig");
const agent_session = @import("../agent/session.zig");
const lit_mod = @import("../core/lit.zig");
const netlist_mod = @import("../circuit/netlist.zig");
const bv = @import("../smt/bv.zig");

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

pub fn runBuiltin(allocator: std.mem.Allocator) !GoldenResult {
    var res: GoldenResult = .{};

    // 1 CNF unsat
    {
        const src = "p cnf 1 2\n1 0\n-1 0\n";
        var cnf = try dimacs.parse(allocator, src);
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .unsat);
    }
    // 2 CNF sat
    {
        const src = "p cnf 2 1\n1 2 0\n";
        var cnf = try dimacs.parse(allocator, src);
        defer cnf.deinit();
        const r = try solver_mod.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&res, r.status == .sat);
    }
    // 3 portfolio unsat
    {
        var cnf = try dimacs.parse(allocator, "p cnf 1 2\n1 0\n-1 0\n");
        defer cnf.deinit();
        const r = try portfolio.solvePortfolio(allocator, &cnf, 100_000);
        defer if (r.model) |m| allocator.free(m);
        pass(&res, r.status == .unsat);
    }
    // 4 PDR stuck0 proven + invariant export
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
    // 5 cert from PDR
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
    // 6 BMC counter violated
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
    // 7 k-induction stuck0
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
    // 8 k-liveness infinite
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
    // 9 CTL AG
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
    // 10 agent session
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
    // 11 BV add
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
    // 12 AIGER parse
    {
        const src =
            \\aag 3 2 0 1 1
            \\2
            \\4
            \\6
            \\6 2 4
        ;
        var nl = try aiger.parse(allocator, src);
        defer nl.deinit();
        pass(&res, nl.inputs.items.len == 2);
    }
    // 13 unique MUS negative (two muses)
    {
        var cnf = @import("../sat/cnf.zig").Cnf.init(allocator);
        defer cnf.deinit();
        cnf.ensureVars(3);
        const a = Lit.positive(Var.fromIndex(0));
        const b = Lit.positive(Var.fromIndex(1));
        const c = Lit.positive(Var.fromIndex(2));
        try cnf.addClause(&.{ a, b });
        try cnf.addClause(&.{ a, c });
        var sol = try solver_mod.Solver.init(allocator, &cnf, .{});
        defer sol.deinit();
        const r = try sol.solveAssumptions(&.{ a.not(), b.not(), c.not() });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        defer if (r.assumption_core) |core| allocator.free(core);
        pass(&res, r.status == .unsat and !r.assumption_core_unique);
    }
    // 14 RUP unsat cert
    {
        var cnf = @import("../sat/cnf.zig").Cnf.init(allocator);
        defer cnf.deinit();
        cnf.ensureVars(1);
        try cnf.addClause(&.{Lit.positive(Var.fromIndex(0))});
        try cnf.addClause(&.{Lit.negative(Var.fromIndex(0))});
        const c = try certificate.unsatWithProof(allocator, &cnf);
        pass(&res, c.unsat and c.proof_clauses >= 1);
    }

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
    try std.testing.expect(r.total >= 12);
}
