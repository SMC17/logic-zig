//! logic-cert — certificate-first flagship (RUP + k-liveness certs).

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next();
    const cmd = iter.next() orelse {
        std.debug.print(
            \\logic-cert — proofs & certificates (profile=cert)
            \\  logic-cert unsat-demo
            \\  logic-cert klive-demo
            \\  logic-cert pdr-demo
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
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
