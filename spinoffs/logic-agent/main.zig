//! logic-agent — multishot / assumptions flagship (profile=agent).

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
            \\logic-agent — multishot SAT + assumptions (profile=agent)
            \\  logic-agent multishot [--queries N] [--vars V]
            \\  logic-agent session-demo
            \\  logic-agent stress [--queries N] [--vars V]
            \\  logic-agent warm-cold [--queries N] [--vars V] [--structured]
            \\  logic-agent assume-demo
            \\  logic-agent profile
            \\
        , .{});
        return;
    };
    const prof = logic.profiles.get(.agent);
    if (std.mem.eql(u8, cmd, "profile")) {
        std.debug.print("profile={s}\n{s}\nmax_conflicts={d}\n", .{
            prof.name,
            prof.blurb,
            prof.solver.max_conflicts,
        });
        return;
    }
    if (std.mem.eql(u8, cmd, "multishot")) {
        var queries: u32 = 40;
        var nvars: u32 = 16;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--queries")) queries = try std.fmt.parseInt(u32, iter.next() orelse "40", 10);
            if (std.mem.eql(u8, a, "--vars")) nvars = try std.fmt.parseInt(u32, iter.next() orelse "16", 10);
        }
        const r = try logic.multishot_bench.run(gpa, io, nvars, queries, 0xA6E17);
        logic.multishot_bench.printResult(&r);
        return;
    }
    if (std.mem.eql(u8, cmd, "stress")) {
        var queries: u32 = 1000;
        var nvars: u32 = 12;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--queries")) queries = try std.fmt.parseInt(u32, iter.next() orelse "1000", 10);
            if (std.mem.eql(u8, a, "--vars")) nvars = try std.fmt.parseInt(u32, iter.next() orelse "12", 10);
        }
        var s = logic.agent_session.Session.init(gpa);
        defer s.deinit();
        const st = try s.stress(queries, nvars, 0x5757E55);
        std.debug.print("AGENT_STRESS queries={d} sat={d} unsat={d} conflicts={d}\n", .{
            st.queries,
            st.sat,
            st.unsat,
            st.conflicts,
        });
        return;
    }
    if (std.mem.eql(u8, cmd, "warm-cold")) {
        var queries: u32 = 200;
        var nvars: u32 = 10;
        var structured = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--queries")) queries = try std.fmt.parseInt(u32, iter.next() orelse "200", 10);
            if (std.mem.eql(u8, a, "--vars")) nvars = try std.fmt.parseInt(u32, iter.next() orelse "10", 10);
            if (std.mem.eql(u8, a, "--structured")) structured = true;
        }
        const c = if (structured)
            try logic.agent_session.compareWarmColdStructured(gpa, @max(nvars, 8), queries)
        else
            try logic.agent_session.compareWarmCold(gpa, nvars, queries, 0xC01D);
        const ratio = if (c.cold_conflicts == 0) 1.0 else @as(f64, @floatFromInt(c.warm_conflicts)) / @as(f64, @floatFromInt(c.cold_conflicts));
        std.debug.print("WARM_COLD mode={s} queries={d} warm_conflicts={d} cold_conflicts={d} ratio={d:.2}\n", .{
            c.mode,
            c.warm_queries,
            c.warm_conflicts,
            c.cold_conflicts,
            ratio,
        });
        return;
    }
    if (std.mem.eql(u8, cmd, "session-demo")) {
        var s = logic.agent_session.Session.init(gpa);
        defer s.deinit();
        s.ensureVars(3);
        const a = logic.Lit.positive(logic.Var.fromIndex(0));
        const b = logic.Lit.positive(logic.Var.fromIndex(1));
        const c = logic.Lit.positive(logic.Var.fromIndex(2));
        try s.addClause(&.{ a, b });
        try s.addClause(&.{ a, c });
        var r1 = try s.query(&.{ a.not(), b.not(), c.not() });
        defer r1.deinit(gpa);
        std.debug.print("q1 unsat unique={} core_len={d} conflicts={d}\n", .{
            r1.core_unique,
            if (r1.core) |core| core.len else 0,
            r1.conflicts,
        });
        var r2 = try s.query(&.{a.not()});
        defer r2.deinit(gpa);
        std.debug.print("q2 sat status={s} queries={d} total_conflicts={d}\n", .{
            @tagName(r2.status),
            s.queries,
            s.total_conflicts,
        });
        return;
    }
    if (std.mem.eql(u8, cmd, "assume-demo")) {
        var cnf = logic.Cnf.init(gpa);
        defer cnf.deinit();
        cnf.ensureVars(2);
        const a = logic.Lit.positive(logic.Var.fromIndex(0));
        const b = logic.Lit.positive(logic.Var.fromIndex(1));
        try cnf.addClause(&.{ a, b });
        var s = try logic.Solver.init(gpa, &cnf, prof.solver);
        defer s.deinit();
        const r = try s.solveAssumptions(&.{ a.not(), b.not() });
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        defer if (r.assumption_core) |c| gpa.free(c);
        std.debug.print("status={s} unique_mus={} core_len={d}\n", .{
            @tagName(r.status),
            r.assumption_core_unique,
            if (r.assumption_core) |c| c.len else 0,
        });
        return;
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
