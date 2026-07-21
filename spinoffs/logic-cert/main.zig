//! logic-cert — certificate-first flagship (RUP + k-liveness + design certs).

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next();
    const cmd = iter.next() orelse {
        std.debug.print(
            \\logic-cert — proofs & certificates (profile=cert)
            \\  logic-cert unsat-demo
            \\  logic-cert klive-demo
            \\  logic-cert pdr-demo
            \\  logic-cert designs
            \\  logic-cert suite          # multi-design cert battery
            \\  logic-cert check-drat <file.cnf>
            \\  logic-cert profile
            \\
        , .{});
        return;
    };
    const prof = logic.profiles.get(.cert);
    if (std.mem.eql(u8, cmd, "profile")) {
        std.debug.print("profile={s}\n{s}\nproof={}\n", .{ prof.name, prof.blurb, prof.solver.proof });
        return;
    }
    if (std.mem.eql(u8, cmd, "unsat-demo")) {
        var cnf = logic.Cnf.init(gpa);
        defer cnf.deinit();
        cnf.ensureVars(1);
        try cnf.addClause(&.{logic.Lit.positive(logic.Var.fromIndex(0))});
        try cnf.addClause(&.{logic.Lit.negative(logic.Var.fromIndex(0))});
        const r = try logic.solveCnf(gpa, &cnf, prof.solver);
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        std.debug.print("status={s} proof_clauses={d}\n", .{
            @tagName(r.status),
            if (r.proof) |p| p.numClauses() else 0,
        });
        if (r.proof) |*p| {
            const ok = try p.verifyRup(gpa, &cnf);
            std.debug.print("internal_rup={s}\n", .{if (ok) "ok" else "FAIL"});
        }
        return;
    }
    if (std.mem.eql(u8, cmd, "klive-demo")) {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        try nl.addJustice(q);
        const cert = try logic.certificate.kLiveCert(gpa, &nl, 4, 16);
        const text = try logic.certificate.writeKLiveCert(gpa, cert);
        defer gpa.free(text);
        std.debug.print("{s}", .{text});
        return;
    }
    if (std.mem.eql(u8, cmd, "pdr-demo")) {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const inv = try logic.certificate.fromPdrProven(gpa, &nl, q, 16);
        if (inv) |*i| {
            defer {
                var ii = i.*;
                ii.deinit();
            }
            const text = try i.writeText(gpa);
            defer gpa.free(text);
            std.debug.print("{s}", .{text});
            std.debug.print("verified={}\n", .{try i.verify(gpa, &nl)});
        } else {
            std.debug.print("no cert\n", .{});
            std.process.exit(1);
        }
        return;
    }
    if (std.mem.eql(u8, cmd, "designs") or std.mem.eql(u8, cmd, "suite")) {
        var ok: u32 = 0;
        var fail: u32 = 0;
        // multi-stuck
        {
            var d = try logic.designs.makeMultiStuck0(gpa, 4);
            defer d.nl.deinit();
            const inv = try logic.certificate.fromPdrProven(gpa, &d.nl, d.bad, 24);
            if (inv) |*i| {
                defer {
                    var ii = i.*;
                    ii.deinit();
                }
                if (try i.verify(gpa, &d.nl) == .verified) ok += 1 else fail += 1;
            } else fail += 1;
        }
        // kind on stuck
        {
            var d = try logic.designs.makeMultiStuck0(gpa, 3);
            defer d.nl.deinit();
            const r = try logic.kinduction.search(gpa, &d.nl, d.bad, 5);
            defer if (r.base.trace) |t| gpa.free(t);
            if (r.status == .proven) ok += 1 else fail += 1;
        }
        // one-hot not violated
        {
            var d = try logic.designs.makeOneHotRing(gpa, 4);
            defer d.nl.deinit();
            var r = try logic.pdr.check(gpa, &d.nl, d.bad, 20);
            defer r.deinit(gpa);
            if (r.status != .violated) ok += 1 else fail += 1;
        }
        // klive one-dead
        {
            var nl = try logic.designs.makeOneDeadAmongToggles(gpa, 4);
            defer nl.deinit();
            const r = try logic.kliveness.checkNetlist(gpa, &nl, 8, 16, 0);
            if (r.status == .proven_infinite) ok += 1 else fail += 1;
        }
        // RUP unit
        {
            var cnf = logic.Cnf.init(gpa);
            defer cnf.deinit();
            cnf.ensureVars(1);
            try cnf.addClause(&.{logic.Lit.positive(logic.Var.fromIndex(0))});
            try cnf.addClause(&.{logic.Lit.negative(logic.Var.fromIndex(0))});
            const c = try logic.certificate.unsatWithProof(gpa, &cnf);
            if (c.unsat and c.proof_clauses >= 1) ok += 1 else fail += 1;
        }
        std.debug.print("CERT_SUITE ok={d} fail={d}\n", .{ ok, fail });
        if (fail != 0) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "check-drat")) {
        const path = iter.next() orelse {
            std.debug.print("missing cnf\n", .{});
            std.process.exit(2);
        };
        const src = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(32 << 20));
        defer gpa.free(src);
        var cnf = try logic.dimacs.parse(gpa, src);
        defer cnf.deinit();
        const r = try logic.drat_external.solveAndCheckExternal(gpa, io, &cnf);
        std.debug.print("status={s} external_drat={s} proof_lines={d}\n", .{
            @tagName(r.status),
            @tagName(r.check),
            r.proof_lines,
        });
        if (r.status == .unsat and r.check == .failed) std.process.exit(1);
        return;
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
