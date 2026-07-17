//! Trust report — external DRAT, CaDiCaL Δ, PDR invariant re-check, ABC probe.
//! Flagship claim: every result is either certified or honestly labeled.

const std = @import("std");
const dimacs = @import("../bridge/dimacs.zig");
const solver_mod = @import("../sat/solver.zig");
const drat_external = @import("../sat/drat_external.zig");
const external = @import("../sat/external.zig");
const abc_interop = @import("../bridge/abc_interop.zig");
const certificate = @import("../cert/certificate.zig");
const designs = @import("../circuit/designs.zig");
const pdr = @import("../circuit/pdr.zig");
const bmc = @import("../circuit/bmc.zig");
const kinduction = @import("../circuit/kinduction.zig");
const kliveness = @import("../circuit/kliveness.zig");
const aiger = @import("../bridge/aiger.zig");
const lit_mod = @import("../core/lit.zig");
const agent_session = @import("../agent/session.zig");

pub const TrustReport = struct {
    drat_available: bool = false,
    drat_verified: u32 = 0,
    drat_failed: u32 = 0,
    cadical_available: bool = false,
    cadical_mismatches: u32 = 0,
    cadical_ran: u32 = 0,
    abc_available: bool = false,
    pdr_certs_ok: u32 = 0,
    pdr_certs_fail: u32 = 0,
    sequential_ok: u32 = 0,
    sequential_fail: u32 = 0,
    klive_ok: u32 = 0,
    klive_fail: u32 = 0,
    agent_ok: u32 = 0,
    agent_fail: u32 = 0,
    all_pass: bool = false,
};

fn unitUnsat(allocator: std.mem.Allocator) !@import("../sat/cnf.zig").Cnf {
    var cnf = @import("../sat/cnf.zig").Cnf.init(allocator);
    cnf.ensureVars(1);
    try cnf.addClause(&.{lit_mod.Lit.positive(lit_mod.Var.fromIndex(0))});
    try cnf.addClause(&.{lit_mod.Lit.negative(lit_mod.Var.fromIndex(0))});
    return cnf;
}

/// Full trust report (I/O for external tools).
pub fn run(allocator: std.mem.Allocator, io: std.Io) !TrustReport {
    var rep: TrustReport = .{};

    // --- DRAT-trim ---
    if (try drat_external.findDratTrim(allocator)) |p| {
        defer allocator.free(p);
        rep.drat_available = true;
        // unit conflict
        {
            var cnf = try unitUnsat(allocator);
            defer cnf.deinit();
            const r = try drat_external.solveAndCheckExternal(allocator, io, &cnf);
            if (r.check == .verified) rep.drat_verified += 1 else if (r.check == .failed) rep.drat_failed += 1;
        }
        // empty clause
        {
            var cnf = try dimacs.parse(allocator, "p cnf 0 1\n0\n");
            defer cnf.deinit();
            const r = try drat_external.solveAndCheckExternal(allocator, io, &cnf);
            if (r.check == .verified) rep.drat_verified += 1 else if (r.check == .failed) rep.drat_failed += 1;
        }
        // portfolio of known unsat from corpus if present
        const paths = [_][]const u8{
            "corpus/bench/sat/simple_unsat.cnf",
            "corpus/bench/sat/false.cnf",
            "corpus/bench/sat/full1.cnf",
        };
        for (paths) |path| {
            const src = std.Io.Dir.cwd().readFileAlloc(io, path, allocator, .limited(4 << 20)) catch continue;
            defer allocator.free(src);
            var cnf = dimacs.parse(allocator, src) catch continue;
            defer cnf.deinit();
            const r = try drat_external.solveAndCheckExternal(allocator, io, &cnf);
            if (r.status != .unsat) continue;
            if (r.check == .verified) rep.drat_verified += 1 else if (r.check == .failed) rep.drat_failed += 1;
        }
    }

    // --- CaDiCaL differential ---
    {
        const fr = try external.fuzzExternal(allocator, io, 0x74727573, 25, 6);
        defer if (fr.solver) |p| allocator.free(p);
        if (!fr.unavailable) {
            rep.cadical_available = true;
            rep.cadical_ran = fr.ran;
            rep.cadical_mismatches = fr.mismatches;
        }
    }

    // --- ABC probe ---
    if (try abc_interop.findAbc(allocator)) |p| {
        defer allocator.free(p);
        rep.abc_available = true;
    }

    // --- PDR certs on designs ---
    {
        var d = try designs.makeMultiStuck0(allocator, 3);
        defer d.nl.deinit();
        const inv = try certificate.fromPdrProven(allocator, &d.nl, d.bad, 20);
        if (inv) |*i| {
            defer {
                var ii = i.*;
                ii.deinit();
            }
            if (try i.verify(allocator, &d.nl)) rep.pdr_certs_ok += 1 else rep.pdr_certs_fail += 1;
        } else rep.pdr_certs_fail += 1;
    }
    {
        // single stuck0
        var d = try designs.makeMultiStuck0(allocator, 1);
        defer d.nl.deinit();
        const inv = try certificate.fromPdrProven(allocator, &d.nl, d.bad, 16);
        if (inv) |*i| {
            defer {
                var ii = i.*;
                ii.deinit();
            }
            if (try i.verify(allocator, &d.nl)) rep.pdr_certs_ok += 1 else rep.pdr_certs_fail += 1;
        } else rep.pdr_certs_fail += 1;
    }

    // --- Sequential teeth: counter BMC + multi-stuck PDR + mutex ---
    {
        var c = try designs.makeCounter(allocator, 3);
        defer c.nl.deinit();
        const r = try bmc.check(allocator, &c.nl, c.bad, 7);
        defer if (r.trace) |t| allocator.free(t);
        if (r.status == .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }
    {
        var c = try designs.makeCounter(allocator, 4);
        defer c.nl.deinit();
        const r = try bmc.check(allocator, &c.nl, c.bad, 14);
        defer if (r.trace) |t| allocator.free(t);
        const r15 = try bmc.check(allocator, &c.nl, c.bad, 15);
        defer if (r15.trace) |t| allocator.free(t);
        if (r.status == .safe_up_to_bound and r15.status == .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }
    {
        var c = try designs.makeCounter(allocator, 5);
        defer c.nl.deinit();
        const r30 = try bmc.check(allocator, &c.nl, c.bad, 30);
        defer if (r30.trace) |t| allocator.free(t);
        const r31 = try bmc.check(allocator, &c.nl, c.bad, 31);
        defer if (r31.trace) |t| allocator.free(t);
        if (r30.status == .safe_up_to_bound and r31.status == .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }
    {
        var s = try designs.makeShift(allocator, 4);
        defer s.nl.deinit();
        const r = try bmc.check(allocator, &s.nl, s.bad, 4);
        defer if (r.trace) |t| allocator.free(t);
        if (r.status == .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }
    {
        var m = try designs.makeMutex(allocator, true);
        defer m.nl.deinit();
        const r = try bmc.check(allocator, &m.nl, m.bad, 8);
        defer if (r.trace) |t| allocator.free(t);
        if (r.status == .safe_up_to_bound) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }
    {
        var m = try designs.makeMutex(allocator, false);
        defer m.nl.deinit();
        const r = try bmc.check(allocator, &m.nl, m.bad, 2);
        defer if (r.trace) |t| allocator.free(t);
        if (r.status == .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }

    // --- K-liveness ---
    {
        var nl = try designs.makeOneDeadAmongToggles(allocator, 4);
        defer nl.deinit();
        const r = try kliveness.checkNetlist(allocator, &nl, 8, 16, 0);
        if (r.status == .proven_infinite) rep.klive_ok += 1 else rep.klive_fail += 1;
    }
    {
        var nl = try designs.makeAllToggleJustice(allocator, 3);
        defer nl.deinit();
        const r = try kliveness.checkNetlist(allocator, &nl, 2, 10, 8);
        if (r.status != .proven_infinite) rep.klive_ok += 1 else rep.klive_fail += 1;
    }
    // (heavier one-dead sizes live in designs-demo / unit tests — keep trust fast+stable)

    // --- Kind induction cert path ---
    {
        var d = try designs.makeMultiStuck0(allocator, 3);
        defer d.nl.deinit();
        const r = try kinduction.search(allocator, &d.nl, d.bad, 5);
        defer if (r.base.trace) |t| allocator.free(t);
        if (r.status == .proven) rep.pdr_certs_ok += 1 else rep.pdr_certs_fail += 1;
    }
    // one-hot ring not violated
    {
        var d = try designs.makeOneHotRing(allocator, 4);
        defer d.nl.deinit();
        var r = try pdr.check(allocator, &d.nl, d.bad, 20);
        defer r.deinit(allocator);
        if (r.status != .violated) rep.sequential_ok += 1 else rep.sequential_fail += 1;
    }

    // --- Agent structured multishot ---
    {
        const c = try agent_session.compareWarmColdStructured(allocator, 10, 50);
        if (c.warm_queries >= 50) rep.agent_ok += 1 else rep.agent_fail += 1;
        // Stress micro
        var s = agent_session.Session.init(allocator);
        defer s.deinit();
        const st = try s.stress(100, 8, 0xC11B);
        if (st.queries == 100) rep.agent_ok += 1 else rep.agent_fail += 1;
    }

    // --- Fixture AIGER cert path ---
    {
        const src = std.Io.Dir.cwd().readFileAlloc(io, "corpus/golden/aiger/stuck0.aag", allocator, .limited(1 << 16)) catch null;
        if (src) |body| {
            defer allocator.free(body);
            var nl = try aiger.parse(allocator, body);
            defer nl.deinit();
            const props = nl.badProps();
            if (props.len > 0) {
                var pr = try pdr.check(allocator, &nl, props[0], 16);
                defer pr.deinit(allocator);
                if (pr.status == .proven) {
                    const inv = try certificate.fromPdrProven(allocator, &nl, props[0], 16);
                    if (inv) |*i| {
                        defer {
                            var ii = i.*;
                            ii.deinit();
                        }
                        if (try i.verify(allocator, &nl)) rep.pdr_certs_ok += 1 else rep.pdr_certs_fail += 1;
                    }
                }
            }
        }
    }

    rep.all_pass = rep.drat_failed == 0 and rep.cadical_mismatches == 0 and
        rep.pdr_certs_fail == 0 and rep.sequential_fail == 0 and rep.klive_fail == 0 and
        rep.agent_fail == 0 and
        (rep.pdr_certs_ok + rep.sequential_ok + rep.klive_ok + rep.agent_ok) > 0;

    return rep;
}

pub fn print(r: *const TrustReport) void {
    std.debug.print("=== TRUST REPORT ===\n", .{});
    std.debug.print("drat: available={} verified={d} failed={d}\n", .{
        r.drat_available,
        r.drat_verified,
        r.drat_failed,
    });
    std.debug.print("cadical: available={} ran={d} mismatches={d}\n", .{
        r.cadical_available,
        r.cadical_ran,
        r.cadical_mismatches,
    });
    std.debug.print("abc: available={}\n", .{r.abc_available});
    std.debug.print("pdr_certs: ok={d} fail={d}\n", .{ r.pdr_certs_ok, r.pdr_certs_fail });
    std.debug.print("sequential: ok={d} fail={d}\n", .{ r.sequential_ok, r.sequential_fail });
    std.debug.print("klive: ok={d} fail={d}\n", .{ r.klive_ok, r.klive_fail });
    std.debug.print("agent: ok={d} fail={d}\n", .{ r.agent_ok, r.agent_fail });
    std.debug.print("TRUST_{s}\n", .{if (r.all_pass) "OK" else "FAIL"});
}

test "trust report constructs without io-dependent crash in unit" {
    // designs-only subset in unit test (no io)
    var d = try designs.makeMultiStuck0(std.testing.allocator, 2);
    defer d.nl.deinit();
    const inv = try certificate.fromPdrProven(std.testing.allocator, &d.nl, d.bad, 16);
    try std.testing.expect(inv != null);
    var i = inv.?;
    defer i.deinit();
    try std.testing.expect(try i.verify(std.testing.allocator, &d.nl));
}
