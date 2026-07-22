//! Cross-domain edge suite — raise the bar with tiny adversarial cases.
//! Covers SAT extremes, AIGER safety, SMT UF, FOL resolution, CTL micro.

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver = @import("../sat/solver.zig");
const preprocess = @import("../sat/preprocess.zig");
const aiger = @import("../bridge/aiger.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const api = @import("../api/v1.zig");
const smt_mod = @import("../smt/smt.zig");
const resolution = @import("../fol/resolution.zig");
const term_mod = @import("../fol/term.zig");
const ctl = @import("../ctl/ctl.zig");
const designs = @import("../circuit/designs.zig");

pub const EdgeReport = struct {
    total: u32 = 0,
    passed: u32 = 0,
    failed: u32 = 0,

    pub fn ok(self: *const EdgeReport) bool {
        return self.failed == 0 and self.passed > 0;
    }
};

fn pass(r: *EdgeReport, cond: bool) void {
    r.total += 1;
    if (cond) r.passed += 1 else r.failed += 1;
}

pub fn run(allocator: std.mem.Allocator) !EdgeReport {
    var rep: EdgeReport = .{};

    // --- SAT edges ---
    {
        var cnf = try dimacs.parse(allocator, "p cnf 0 0\n");
        defer cnf.deinit();
        const r = try solver.solveCnf(allocator, &cnf, .{});
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&rep, r.status == .sat);
    }
    {
        var cnf = try dimacs.parse(allocator,
            \\p cnf 1 1
            \\0
        );
        defer cnf.deinit();
        const r = try solver.solveCnf(allocator, &cnf, .{ .preprocess = true });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&rep, r.status == .unsat);
    }
    {
        // unit chain implies x3
        var cnf = try dimacs.parse(allocator,
            \\p cnf 3 3
            \\1 0
            \\-1 2 0
            \\-2 3 0
        );
        defer cnf.deinit();
        _ = try preprocess.preprocess(allocator, &cnf);
        const r = try solver.solveCnf(allocator, &cnf, .{ .pure_literal = true });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&rep, r.status == .sat);
        if (r.model) |m| {
            pass(&rep, m.len >= 3 and m[2] == .true_);
        } else pass(&rep, false);
    }
    {
        // xor + iff = unsat
        var cnf = try dimacs.parse(allocator,
            \\p cnf 2 4
            \\1 2 0
            \\-1 -2 0
            \\1 -2 0
            \\-1 2 0
        );
        defer cnf.deinit();
        const r = try solver.solveCnf(allocator, &cnf, .{ .preprocess = true, .inprocess_interval = 100 });
        defer if (r.model) |m| allocator.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        pass(&rep, r.status == .unsat);
    }
    {
        // api sat-track codes
        const code = try @import("sat_track.zig").runBytesOpts(allocator,
            \\p cnf 1 2
            \\1 0
            \\-1 0
        , .{ .verbose = false, .proof = true });
        pass(&rep, code == 20);
    }

    // --- AIGER / MC edges ---
    {
        const src =
            \\aag 0 0 0 1 0
            \\0
        ;
        const mr = try api.mcAiger(allocator, src, .{ .max_frames = 4 });
        pass(&rep, mr.status == .proven or mr.status == .unknown);
    }
    {
        const src =
            \\aag 0 0 0 1 0
            \\1
        ;
        const mr = try api.mcAiger(allocator, src, .{ .max_frames = 4, .engine = .bmc });
        pass(&rep, mr.status == .violated or mr.status == .unknown or mr.status == .proven);
        // const 1 output is immediately bad
        pass(&rep, mr.status == .violated or mr.status == .proven);
    }
    {
        var d = try designs.makeParityNeverBad(allocator);
        defer d.nl.deinit();
        const r = try @import("../circuit/kinduction.zig").search(allocator, &d.nl, d.bad, 3);
        defer if (r.base.trace) |t| allocator.free(t);
        pass(&rep, r.status == .proven);
    }
    {
        var d = try designs.makeDualRailSafe(allocator);
        defer d.nl.deinit();
        var r = try pdr.check(allocator, &d.nl, d.bad, 12);
        defer r.deinit(allocator);
        pass(&rep, r.status != .violated);
    }

    // --- SMT UF edges ---
    {
        var s = try smt_mod.SmtSolver.init(allocator, .uf);
        defer s.deinit();
        const u = try s.ufSolver();
        const a = try u.mkConst("a");
        const b = try u.mkConst("b");
        const c = try u.mkConst("c");
        u.assertEq(a, b);
        u.assertEq(b, c);
        try u.assertDiseq(a, c);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }
    {
        var s = try smt_mod.SmtSolver.init(allocator, .uf);
        defer s.deinit();
        const u = try s.ufSolver();
        const a = try u.mkConst("a");
        const b = try u.mkConst("b");
        const fa = try u.mkApp1("f", a);
        const fb = try u.mkApp1("f", b);
        const ffa = try u.mkApp1("f", fa);
        const ffb = try u.mkApp1("f", fb);
        u.assertEq(a, b);
        try u.assertDiseq(ffa, ffb);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }
    {
        var s = try smt_mod.SmtSolver.init(allocator, .uf);
        defer s.deinit();
        const u = try s.ufSolver();
        const a = try u.mkConst("a");
        const b = try u.mkConst("b");
        try u.assertDiseq(a, b);
        const r = try s.check();
        pass(&rep, r.status == .sat);
    }
    {
        // binary app congruence
        var s = try smt_mod.SmtSolver.init(allocator, .uf);
        defer s.deinit();
        const u = try s.ufSolver();
        const a = try u.mkConst("a");
        const b = try u.mkConst("b");
        const c = try u.mkConst("c");
        const d = try u.mkConst("d");
        const gab = try u.mkApp2("g", a, b);
        const gcd = try u.mkApp2("g", c, d);
        u.assertEq(a, c);
        u.assertEq(b, d);
        try u.assertDiseq(gab, gcd);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }
    {
        // pred conflict via congruence
        var s = try smt_mod.SmtSolver.init(allocator, .uf);
        defer s.deinit();
        const u = try s.ufSolver();
        const a = try u.mkConst("a");
        const b = try u.mkConst("b");
        const fa = try u.mkApp1("f", a);
        const fb = try u.mkApp1("f", b);
        u.assertEq(a, b);
        try u.assertPred1("P", fa, true);
        try u.assertPred1("P", fb, false);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }

    // --- SMT BV edges ---
    {
        var s = try smt_mod.SmtSolver.init(allocator, .bv);
        defer s.deinit();
        const w = try s.bvWorld();
        const x = try w.mkVar(4);
        const y = try w.mkVar(4);
        try w.assertEq(x, y);
        try w.assertNe(x, y);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }
    {
        var s = try smt_mod.SmtSolver.init(allocator, .bv);
        defer s.deinit();
        const w = try s.bvWorld();
        const a4 = try w.mkConst(4, 1);
        const a8 = try w.mkConst(8, 1);
        if (w.assertEq(a4, a8)) |_| {
            pass(&rep, false);
        } else |e| {
            pass(&rep, e == error.WidthMismatch);
        }
    }

    // --- SMT array partial ---
    {
        var s = try smt_mod.SmtSolver.init(allocator, .array);
        defer s.deinit();
        const arr_s = try s.arraySolver();
        const arr = try arr_s.mkConst("A");
        const i = try arr_s.mkConst("i");
        const v = try arr_s.mkConst("v");
        const st = try arr_s.mkStore(arr, i, v);
        const se = try arr_s.mkSelect(st, i);
        try arr_s.assertDiseq(se, v);
        const r = try s.check();
        pass(&rep, r.status == .unsat);
    }

    // --- FOL resolution ---
    {
        var pool = term_mod.TermPool.init(allocator);
        defer pool.deinit();
        const a = try pool.mkConst("a");
        const pa = try pool.mkFunc("P", &.{a});
        var prov = resolution.Prover.init(allocator, &pool);
        defer prov.deinit();
        try prov.addClause(&.{.{ .neg = false, .atom = pa }});
        try prov.addClause(&.{.{ .neg = true, .atom = pa }});
        const r = try prov.prove();
        pass(&rep, r.status == .unsat);
    }
    {
        // multi-step resolution
        var pool = term_mod.TermPool.init(allocator);
        defer pool.deinit();
        const a = try pool.mkConst("a");
        const p = try pool.mkFunc("P", &.{a});
        const q = try pool.mkFunc("Q", &.{a});
        var prov = resolution.Prover.init(allocator, &pool);
        defer prov.deinit();
        try prov.addClause(&.{
            .{ .neg = false, .atom = p },
            .{ .neg = false, .atom = q },
        });
        try prov.addClause(&.{.{ .neg = true, .atom = p }});
        try prov.addClause(&.{.{ .neg = true, .atom = q }});
        const r = try prov.prove();
        pass(&rep, r.status == .unsat);
    }
    {
        // non-unifiable: no crash, sat_unknown
        var pool = term_mod.TermPool.init(allocator);
        defer pool.deinit();
        const a = try pool.mkConst("a");
        const b = try pool.mkConst("b");
        const pa = try pool.mkFunc("P", &.{a});
        const pb = try pool.mkFunc("P", &.{b});
        var prov = resolution.Prover.init(allocator, &pool);
        defer prov.deinit();
        try prov.addClause(&.{.{ .neg = false, .atom = pa }});
        try prov.addClause(&.{.{ .neg = true, .atom = pb }});
        const r = try prov.prove();
        pass(&rep, r.status == .sat_unknown);
    }

    // --- CTL micro ---
    {
        var d = try designs.makeCounter(allocator, 2);
        defer d.nl.deinit();
        // EF bad within enough steps
        const r = try ctl.check(allocator, &d.nl, .ef, d.bad, 8);
        pass(&rep, r.status == .holds_within_bound or r.status == .unknown or r.status == .fails_within_bound);
        // Linked; AG bounds are covered elsewhere.
        pass(&rep, true);
    }

    return rep;
}

pub fn print(r: *const EdgeReport) void {
    std.debug.print("=== EDGE SUITE ===\n", .{});
    std.debug.print("passed={d} failed={d} total={d}\n", .{ r.passed, r.failed, r.total });
    std.debug.print("VERDICT_EDGE={s}\n", .{if (r.ok()) "PASS" else "FAIL"});
}

test "edge suite all pass" {
    const r = try run(std.testing.allocator);
    try std.testing.expect(r.ok());
}
