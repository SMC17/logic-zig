//! logic-zig CLI — propositional analysis front door.

const std = @import("std");
const logic = @import("logic");

const usage =
    \\logic-zig — prop / CDCL / PDR / IPASIR / competition tracks / benches
    \\
    \\Usage:
    \\  logic-zig sat <formula|--file path.cnf> [--proof] [--dump-proof PATH] [--check-drat]
    \\  logic-zig sat-track <file.cnf> [--max-conflicts N] [--portfolio] [--proof] [--quiet]
    \\  logic-zig hwmcc-track <file.aag|aig> [--frames N] [--each] [--justice] [--lasso] [--cert] [--no-kind]
    \\  logic-zig fuzz / miter / unify / eval / cnf / tautology / equiv
    \\  logic-zig bmc-demo / kind-demo / ic3-demo / pdr-demo
    \\  logic-zig aiger <file.aag|aig>
    \\  logic-zig aiger-write <in.aag|aig> <out.aag> [--binary] [--extended]
    \\  logic-zig justice-demo [--bound K] [--lasso]
    \\  logic-zig klive-demo [--max-k K]        # infinite justice proof (k-liveness)
    \\  logic-zig abduce-demo                   # observation → minimal causes (diagnosis)
    \\  logic-zig induce-demo                   # examples → minimal-k DNF rule
    \\  logic-zig reason-demo                   # min-cost abduce · ALP · Bayes · defaults · KLM
    \\  logic-zig ternary-demo
    \\  logic-zig doctor                        # self-check smoke suite
    \\  logic-zig api-info                      # stable api/v1 version + capabilities
    \\  logic-zig edge-suite                    # cross-domain adversarial edges
    \\  logic-zig taxonomy                      # universal named-systems registry
    \\  logic-zig giants                        # discover Kissat/Z3/ABC/Vampire/…
    \\  logic-zig trust-report                  # DRAT + CaDiCaL + PDR certs + sequential
    \\  logic-zig sat-scoreboard [--dir DIR] [--limit N] [--conflicts N] [--portfolio] [--industrial]
    \\  logic-zig abc-delta <file.aag> [--frames N]   # internal MC vs ABC when present
    \\  logic-zig diff-external [--iters N]
    \\  logic-zig bench-suite [--dir DIR] [--timeout S] [--max-conflicts N] [--json] [--fair]
    \\  logic-zig bench-comp [--dir DIR] [--timeout S] [--max-conflicts N] [--no-drat]
    \\  logic-zig bench-multishot [--vars N] [--queries N] [--seed S]
    \\  logic-zig hwmcc-bench [--frames N] [--dir DIR]
    \\  logic-zig win-report [--comp]         # full scoreboard (+ competition slice)
    \\  logic-zig correctness-suite [--dir DIR] [--ext-iters N]
    \\  logic-zig help
    \\
;

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    const io = init.io;
    var iter = try std.process.Args.Iterator.initAllocator(init.minimal.args, gpa);
    defer iter.deinit();
    _ = iter.next(); // argv0

    const cmd = iter.next() orelse {
        std.debug.print("{s}", .{usage});
        std.process.exit(2);
    };

    if (std.mem.eql(u8, cmd, "help") or std.mem.eql(u8, cmd, "-h") or std.mem.eql(u8, cmd, "--help")) {
        std.debug.print("{s}", .{usage});
        return;
    }

    if (std.mem.eql(u8, cmd, "sat")) {
        var proof = false;
        var check_drat = false;
        var dump_proof: ?[]const u8 = null;
        var file_mode = false;
        var formula_or_path: ?[]const u8 = null;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--proof")) {
                proof = true;
            } else if (std.mem.eql(u8, a, "--check-drat")) {
                check_drat = true;
                proof = true;
            } else if (std.mem.eql(u8, a, "--dump-proof")) {
                dump_proof = iter.next() orelse return fail("dump-proof path");
                proof = true;
            } else if (std.mem.eql(u8, a, "--file") or std.mem.eql(u8, a, "-f")) {
                file_mode = true;
            } else if (formula_or_path == null) {
                formula_or_path = a;
            }
        }
        const arg = formula_or_path orelse return fail("missing formula or path");
        if (file_mode) {
            try cmdSatFile(gpa, io, arg, proof, dump_proof, check_drat);
        } else {
            try cmdSatFormula(gpa, arg, proof);
        }
        return;
    }
    if (std.mem.eql(u8, cmd, "fuzz")) {
        var iters: u32 = 50;
        var nvars: u32 = 8;
        var seed: u64 = 0xC0FFEE;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--iters")) {
                iters = std.fmt.parseInt(u32, iter.next() orelse return fail("iters"), 10) catch return fail("bad iters");
            } else if (std.mem.eql(u8, a, "--vars")) {
                nvars = std.fmt.parseInt(u32, iter.next() orelse return fail("vars"), 10) catch return fail("bad vars");
            } else if (std.mem.eql(u8, a, "--seed")) {
                seed = std.fmt.parseInt(u64, iter.next() orelse return fail("seed"), 10) catch return fail("bad seed");
            }
        }
        try cmdFuzz(gpa, iters, nvars, seed);
        return;
    }
    if (std.mem.eql(u8, cmd, "miter")) {
        const a = iter.next() orelse return fail("missing a.json");
        const b = iter.next() orelse return fail("missing b.json");
        try cmdMiter(gpa, io, a, b);
        return;
    }
    if (std.mem.eql(u8, cmd, "unify")) {
        const t1 = iter.next() orelse return fail("missing term1");
        const t2 = iter.next() orelse return fail("missing term2");
        try cmdUnify(gpa, t1, t2);
        return;
    }
    if (std.mem.eql(u8, cmd, "bmc-demo")) {
        var bound: u32 = 3;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--bound")) {
                bound = std.fmt.parseInt(u32, iter.next() orelse return fail("bound"), 10) catch return fail("bad bound");
            }
        }
        try cmdBmcDemo(gpa, bound);
        return;
    }
    if (std.mem.eql(u8, cmd, "kind-demo")) {
        var max_k: u32 = 5;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--max-k")) {
                max_k = std.fmt.parseInt(u32, iter.next() orelse return fail("max-k"), 10) catch return fail("bad max-k");
            }
        }
        try cmdKindDemo(gpa, max_k);
        return;
    }
    if (std.mem.eql(u8, cmd, "ic3-demo") or std.mem.eql(u8, cmd, "pdr-demo")) {
        var frames: u32 = 12;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = std.fmt.parseInt(u32, iter.next() orelse return fail("frames"), 10) catch return fail("bad frames");
            }
        }
        try cmdIc3Demo(gpa, frames);
        return;
    }
    if (std.mem.eql(u8, cmd, "aiger")) {
        const path = iter.next() orelse return fail("missing aag/aig path");
        try cmdAiger(gpa, io, path);
        return;
    }
    if (std.mem.eql(u8, cmd, "aiger-write")) {
        const inp = iter.next() orelse return fail("missing input");
        const outp = iter.next() orelse return fail("missing output");
        var binary = false;
        var extended = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--binary")) binary = true;
            if (std.mem.eql(u8, a, "--extended")) extended = true;
        }
        try cmdAigerWrite(gpa, io, inp, outp, binary, extended);
        return;
    }
    if (std.mem.eql(u8, cmd, "justice-demo")) {
        var bound: u32 = 3;
        var lasso = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--bound")) {
                bound = std.fmt.parseInt(u32, iter.next() orelse return fail("bound"), 10) catch return fail("bad bound");
            } else if (std.mem.eql(u8, a, "--lasso")) {
                lasso = true;
            }
        }
        try cmdJusticeDemo(gpa, bound, lasso);
        return;
    }
    if (std.mem.eql(u8, cmd, "klive-demo")) {
        var max_k: u32 = 4;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--max-k")) {
                max_k = std.fmt.parseInt(u32, iter.next() orelse return fail("max-k"), 10) catch return fail("bad max-k");
            }
        }
        try cmdKliveDemo(gpa, max_k);
        return;
    }
    if (std.mem.eql(u8, cmd, "abduce-demo")) {
        try cmdAbduceDemo(gpa);
        return;
    }
    if (std.mem.eql(u8, cmd, "induce-demo")) {
        try cmdInduceDemo(gpa);
        return;
    }
    if (std.mem.eql(u8, cmd, "reason-demo")) {
        try cmdReasonDemo(gpa);
        return;
    }
    if (std.mem.eql(u8, cmd, "ternary-demo")) {
        try cmdTernaryDemo(gpa);
        return;
    }
    if (std.mem.eql(u8, cmd, "doctor")) {
        try cmdDoctor(gpa, io);
        return;
    }
    if (std.mem.eql(u8, cmd, "api-info")) {
        const line = try logic.api.versionLine(gpa);
        defer gpa.free(line);
        std.debug.print("{s}\n", .{line});
        const caps = logic.api.Capability.current();
        std.debug.print("capabilities:\n", .{});
        std.debug.print("  sat_cdcl={} sat_portfolio={} sat_preprocess={} sat_proof_rup={}\n", .{
            caps.sat_cdcl, caps.sat_portfolio, caps.sat_preprocess, caps.sat_proof_rup,
        });
        std.debug.print("  mc_bmc={} mc_kind={} mc_pdr={} mc_klive={}\n", .{
            caps.mc_bmc, caps.mc_kind, caps.mc_pdr, caps.mc_klive,
        });
        std.debug.print("  smt_bv={} smt_uf={} smt_array={}\n", .{ caps.smt_bv, caps.smt_uf, caps.smt_array });
        std.debug.print("  fol_unify={} fol_finite_model={} fol_resolution={}\n", .{
            caps.fol_unify, caps.fol_finite_model, caps.fol_resolution,
        });
        std.debug.print("  ctl_bounded={} agent_session={} abc_interop={}\n", .{
            caps.ctl_bounded, caps.agent_session, caps.abc_interop,
        });
        std.debug.print("  reason_abduce={} reason_induce={} reason_abduce_cost={} sat_maxsat={}\n", .{
            caps.reason_abduce, caps.reason_induce, caps.reason_abduce_cost, caps.sat_maxsat,
        });
        std.debug.print("  reason_alp={} reason_bayes={} reason_default={} reason_klm={}\n", .{
            caps.reason_alp, caps.reason_bayes, caps.reason_default, caps.reason_klm,
        });
        std.debug.print("  reason_af={} reason_asp={} reason_agm={} reason_circ={} reason_analogy={}\n", .{
            caps.reason_af, caps.reason_asp, caps.reason_agm, caps.reason_circ, caps.reason_analogy,
        });
        std.debug.print("program: docs/INDUSTRIAL.md\n", .{});
        return;
    }
    if (std.mem.eql(u8, cmd, "edge-suite")) {
        const r = try logic.edge_suite.run(gpa);
        logic.edge_suite.print(&r);
        if (!r.ok()) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "taxonomy")) {
        logic.taxonomy.printAll();
        return;
    }
    if (std.mem.eql(u8, cmd, "giants")) {
        try logic.giants.printDiscover(gpa);
        return;
    }
    if (std.mem.eql(u8, cmd, "trust-report")) {
        const rep = try logic.trust_report.run(gpa, io);
        logic.trust_report.print(&rep);
        if (!rep.all_pass) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "sat-track")) {
        var path: ?[]const u8 = null;
        var opts: logic.sat_track.TrackOpts = .{};
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--max-conflicts")) {
                opts.max_conflicts = std.fmt.parseInt(u64, iter.next() orelse return fail("max-conflicts"), 10) catch return fail("bad max-conflicts");
            } else if (std.mem.eql(u8, a, "--portfolio")) {
                opts.portfolio = true;
            } else if (std.mem.eql(u8, a, "--proof")) {
                opts.proof = true;
            } else if (std.mem.eql(u8, a, "--quiet")) {
                opts.verbose = false;
            } else if (std.mem.eql(u8, a, "--budget")) {
                opts.portfolio_budget = std.fmt.parseInt(u64, iter.next() orelse return fail("budget"), 10) catch return fail("bad budget");
            } else if (path == null) {
                path = a;
            }
        }
        const code = try logic.sat_track.runFileOpts(gpa, path orelse return fail("missing cnf"), io, opts);
        std.process.exit(code);
    }
    if (std.mem.eql(u8, cmd, "hwmcc-track")) {
        var frames: u32 = 16;
        var path: ?[]const u8 = null;
        var each = false;
        var just = false;
        var lasso = false;
        var cert = false;
        var use_kind = true;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = std.fmt.parseInt(u32, iter.next() orelse return fail("frames"), 10) catch return fail("bad frames");
            } else if (std.mem.eql(u8, a, "--each")) {
                each = true;
            } else if (std.mem.eql(u8, a, "--justice")) {
                just = true;
            } else if (std.mem.eql(u8, a, "--lasso")) {
                lasso = true;
            } else if (std.mem.eql(u8, a, "--cert")) {
                cert = true;
            } else if (std.mem.eql(u8, a, "--no-kind")) {
                use_kind = false;
            } else if (path == null) path = a;
        }
        const code = try logic.hwmcc_track.runFileOpts(gpa, path orelse return fail("missing aiger"), io, .{
            .max_frames = frames,
            .each = each,
            .justice = just,
            .lasso = lasso,
            .cert = cert,
            .kind = use_kind,
        });
        std.process.exit(code);
    }
    if (std.mem.eql(u8, cmd, "sat-scoreboard")) {
        var dir: []const u8 = "corpus/bench/sat_comp";
        var limit: u32 = 30;
        var conflicts: u64 = 300_000;
        var use_portfolio = false;
        var industrial = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--dir")) {
                dir = iter.next() orelse return fail("dir");
            } else if (std.mem.eql(u8, a, "--limit")) {
                limit = std.fmt.parseInt(u32, iter.next() orelse return fail("limit"), 10) catch return fail("bad limit");
            } else if (std.mem.eql(u8, a, "--conflicts")) {
                conflicts = std.fmt.parseInt(u64, iter.next() orelse return fail("conflicts"), 10) catch return fail("bad conflicts");
            } else if (std.mem.eql(u8, a, "--portfolio")) {
                use_portfolio = true;
            } else if (std.mem.eql(u8, a, "--industrial") or std.mem.eql(u8, a, "--hard")) {
                industrial = true;
            }
        }
        var sb = try logic.sat_scoreboard.run(gpa, io, .{
            .suite_dir = dir,
            .limit = limit,
            .max_conflicts = conflicts,
            .portfolio = use_portfolio,
            .portfolio_budget = conflicts,
            .preprocess = true,
            .inprocess = true,
            .industrial = industrial,
            .timeout_s = if (industrial) 30.0 else 10.0,
        });
        defer sb.deinit(gpa);
        logic.sat_scoreboard.print(&sb);
        if (!sb.correctnessOk()) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "abc-delta")) {
        var path: ?[]const u8 = null;
        var frames: u32 = 16;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = std.fmt.parseInt(u32, iter.next() orelse return fail("frames"), 10) catch return fail("bad frames");
            } else if (path == null) path = a;
        }
        const aig = path orelse return fail("missing aiger");
        const src = try std.Io.Dir.cwd().readFileAlloc(io, aig, gpa, .limited(32 * 1024 * 1024));
        defer gpa.free(src);
        const mr = try logic.api.mcAiger(gpa, src, .{ .max_frames = frames, .engine = .auto, .cert = false });
        const ar = try logic.abc_interop.checkAigerSafety(gpa, io, aig);
        defer {
            var aa = ar;
            aa.deinit(gpa);
        }
        const proven = mr.status == .proven;
        const violated = mr.status == .violated;
        const label = logic.abc_interop.deltaLabel(proven, violated, ar.status);
        std.debug.print("internal={s} engine={s} abc={s} delta={s}\n", .{
            @tagName(mr.status),
            mr.engine,
            @tagName(ar.status),
            label,
        });
        if (std.mem.eql(u8, label, "MISMATCH")) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "diff-external")) {
        var iters: u32 = 20;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--iters")) {
                iters = std.fmt.parseInt(u32, iter.next() orelse return fail("iters"), 10) catch return fail("bad iters");
            }
        }
        try cmdDiffExternal(gpa, io, iters);
        return;
    }
    if (std.mem.eql(u8, cmd, "bench-suite")) {
        var dir: []const u8 = "corpus/bench/sat";
        var timeout_s: f64 = 5.0;
        var max_conflicts: u64 = 2_000_000;
        var json = false;
        var fair = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--dir")) {
                dir = iter.next() orelse return fail("dir");
            } else if (std.mem.eql(u8, a, "--timeout")) {
                timeout_s = std.fmt.parseFloat(f64, iter.next() orelse return fail("timeout")) catch return fail("bad timeout");
            } else if (std.mem.eql(u8, a, "--max-conflicts")) {
                max_conflicts = std.fmt.parseInt(u64, iter.next() orelse return fail("max-conflicts"), 10) catch return fail("bad max-conflicts");
            } else if (std.mem.eql(u8, a, "--json")) {
                json = true;
            } else if (std.mem.eql(u8, a, "--fair")) {
                fair = true;
            }
        }
        try cmdBenchSuite(gpa, io, dir, timeout_s, max_conflicts, json, fair);
        return;
    }
    if (std.mem.eql(u8, cmd, "bench-multishot")) {
        var nvars: u32 = 24;
        var queries: u32 = 80;
        var seed: u64 = 0xA11CE;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--vars")) {
                nvars = std.fmt.parseInt(u32, iter.next() orelse return fail("vars"), 10) catch return fail("bad vars");
            } else if (std.mem.eql(u8, a, "--queries")) {
                queries = std.fmt.parseInt(u32, iter.next() orelse return fail("queries"), 10) catch return fail("bad queries");
            } else if (std.mem.eql(u8, a, "--seed")) {
                seed = std.fmt.parseInt(u64, iter.next() orelse return fail("seed"), 10) catch return fail("bad seed");
            }
        }
        try cmdBenchMultishot(gpa, io, nvars, queries, seed);
        return;
    }
    if (std.mem.eql(u8, cmd, "correctness-suite")) {
        var dir: []const u8 = "corpus/bench/sat";
        var ext_iters: u32 = 40;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--dir")) {
                dir = iter.next() orelse return fail("dir");
            } else if (std.mem.eql(u8, a, "--ext-iters")) {
                ext_iters = std.fmt.parseInt(u32, iter.next() orelse return fail("ext-iters"), 10) catch return fail("bad ext-iters");
            }
        }
        try cmdCorrectnessSuite(gpa, io, dir, ext_iters);
        return;
    }
    if (std.mem.eql(u8, cmd, "hwmcc-bench")) {
        var frames: u32 = 12;
        var dir: []const u8 = "corpus/bench/hwmcc";
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--frames")) {
                frames = std.fmt.parseInt(u32, iter.next() orelse return fail("frames"), 10) catch return fail("bad frames");
            } else if (std.mem.eql(u8, a, "--dir")) {
                dir = iter.next() orelse return fail("dir");
            }
        }
        try cmdHwmccBench(gpa, io, frames, dir);
        return;
    }
    if (std.mem.eql(u8, cmd, "win-report")) {
        var with_comp = false;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--comp")) with_comp = true;
        }
        try cmdWinReport(gpa, io, with_comp);
        return;
    }
    if (std.mem.eql(u8, cmd, "bench-comp")) {
        var dir: []const u8 = "corpus/bench/sat_comp";
        var timeout_s: f64 = 5.0;
        var max_conflicts: u64 = 5_000_000;
        var check_drat = true;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--dir")) {
                dir = iter.next() orelse return fail("dir");
            } else if (std.mem.eql(u8, a, "--timeout")) {
                timeout_s = std.fmt.parseFloat(f64, iter.next() orelse return fail("timeout")) catch return fail("bad timeout");
            } else if (std.mem.eql(u8, a, "--max-conflicts")) {
                max_conflicts = std.fmt.parseInt(u64, iter.next() orelse return fail("max-conflicts"), 10) catch return fail("bad max-conflicts");
            } else if (std.mem.eql(u8, a, "--no-drat")) {
                check_drat = false;
            }
        }
        try cmdBenchComp(gpa, io, dir, timeout_s, max_conflicts, check_drat);
        return;
    }
    if (std.mem.eql(u8, cmd, "unsat")) {
        const f = iter.next() orelse return fail("missing formula");
        try cmdUnsat(gpa, f);
        return;
    }
    if (std.mem.eql(u8, cmd, "tautology")) {
        const f = iter.next() orelse return fail("missing formula");
        try cmdTautology(gpa, f);
        return;
    }
    if (std.mem.eql(u8, cmd, "equiv")) {
        const f1 = iter.next() orelse return fail("missing formula1");
        const f2 = iter.next() orelse return fail("missing formula2");
        try cmdEquiv(gpa, f1, f2);
        return;
    }
    if (std.mem.eql(u8, cmd, "simplify")) {
        const f = iter.next() orelse return fail("missing formula");
        try cmdSimplify(gpa, f);
        return;
    }
    if (std.mem.eql(u8, cmd, "cnf")) {
        const f = iter.next() orelse return fail("missing formula");
        try cmdCnf(gpa, f);
        return;
    }
    if (std.mem.eql(u8, cmd, "eval")) {
        const f = iter.next() orelse return fail("missing formula");
        var assign_str: ?[]const u8 = null;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--assign")) {
                assign_str = iter.next();
            }
        }
        try cmdEval(gpa, f, assign_str orelse return fail("missing --assign"));
        return;
    }

    std.debug.print("unknown command: {s}\n{s}", .{ cmd, usage });
    std.process.exit(2);
}

fn fail(msg: []const u8) error{Cli} {
    std.debug.print("error: {s}\n", .{msg});
    std.process.exit(2);
}

fn cmdSatFormula(gpa: std.mem.Allocator, formula: []const u8, proof: bool) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");
    const q = try logic.satFormulaOpts(gpa, &pool, e, .{ .proof = proof });
    defer if (q.model) |m| gpa.free(m);
    switch (q.status) {
        .sat => {
            std.debug.print("SAT\n", .{});
            if (q.model) |m| {
                for (m, 0..) |v, i| {
                    const name = pool.varName(logic.Var.fromIndex(@intCast(i)));
                    const bit: u8 = if (v == .true_) 1 else 0;
                    std.debug.print("  {s}={d}\n", .{ name, bit });
                }
            }
            std.debug.print("conflicts={d} learned={d}\n", .{ q.conflicts, q.learned });
        },
        .unsat => {
            std.debug.print("UNSAT\n", .{});
            std.debug.print("conflicts={d} learned={d}\n", .{ q.conflicts, q.learned });
        },
        .unknown => std.debug.print("UNKNOWN\n", .{}),
    }
}

fn cmdSatFile(
    gpa: std.mem.Allocator,
    io: std.Io,
    path: []const u8,
    proof: bool,
    dump_proof: ?[]const u8,
    check_drat: bool,
) !void {
    const src = std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(64 * 1024 * 1024)) catch return fail("read file failed");
    defer gpa.free(src);
    var cnf = logic.dimacs.parse(gpa, src) catch return fail("dimacs parse error");
    defer cnf.deinit();
    const r = try logic.solveCnf(gpa, &cnf, .{ .proof = proof });
    defer if (r.model) |m| gpa.free(m);
    defer if (r.proof) |*p| {
        var pp = p.*;
        pp.deinit();
    };
    switch (r.status) {
        .sat => {
            std.debug.print("SAT\n", .{});
            if (r.model) |m| {
                if (!cnf.checkModel(m)) return fail("internal: model failed check");
                for (m, 0..) |v, i| {
                    if (v == .true_) {
                        std.debug.print("  {d}\n", .{i + 1});
                    } else {
                        std.debug.print("  -{d}\n", .{i + 1});
                    }
                }
            }
        },
        .unsat => {
            std.debug.print("UNSAT\n", .{});
            if (r.proof) |p| {
                std.debug.print("proof_clauses={d} (RUP verified)\n", .{p.numClauses()});
                if (dump_proof) |dp| {
                    var aw: std.Io.Writer.Allocating = .init(gpa);
                    defer aw.deinit();
                    try p.writeDimacsLike(&aw.writer);
                    const body = try aw.toOwnedSlice();
                    defer gpa.free(body);
                    var path_z: [512]u8 = undefined;
                    if (dp.len >= path_z.len) return fail("path too long");
                    @memcpy(path_z[0..dp.len], dp);
                    path_z[dp.len] = 0;
                    const fd = std.os.linux.open(@ptrCast(&path_z), .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, 0o644);
                    if (@as(isize, @bitCast(fd)) < 0) return fail("open proof failed");
                    _ = std.os.linux.write(@intCast(fd), body.ptr, body.len);
                    _ = std.os.linux.close(@intCast(fd));
                    std.debug.print("dumped_proof={s} bytes={d}\n", .{ dp, body.len });
                }
                if (check_drat) {
                    const chk = try logic.drat_external.checkProofExternal(gpa, io, &cnf, &p);
                    std.debug.print("external_drat={s}\n", .{@tagName(chk)});
                    if (chk == .failed or chk == .internal_error) std.process.exit(1);
                }
            }
        },
        .unknown => std.debug.print("UNKNOWN\n", .{}),
    }
    std.debug.print("conflicts={d} learned={d}\n", .{ r.conflicts, r.learned });
}

fn cmdFuzz(gpa: std.mem.Allocator, iters: u32, nvars: u32, seed: u64) !void {
    if (nvars > 16) return fail("vars must be <= 16 for brute oracle");
    const mm = try logic.fuzz.fuzzVsBrute(gpa, seed, iters, nvars, 4.2);
    if (mm == 0) {
        std.debug.print("FUZZ_OK iters={d} vars={d} seed={d} mismatches=0\n", .{ iters, nvars, seed });
    } else {
        std.debug.print("FUZZ_FAIL mismatches={d}\n", .{mm});
        std.process.exit(1);
    }
}

fn cmdMiter(gpa: std.mem.Allocator, io: std.Io, path_a: []const u8, path_b: []const u8) !void {
    const sa = std.Io.Dir.cwd().readFileAlloc(io, path_a, gpa, .limited(16 * 1024 * 1024)) catch return fail("read a failed");
    defer gpa.free(sa);
    const sb = std.Io.Dir.cwd().readFileAlloc(io, path_b, gpa, .limited(16 * 1024 * 1024)) catch return fail("read b failed");
    defer gpa.free(sb);
    var na = logic.yosys_json.parseModule(gpa, sa, null) catch return fail("parse a json failed");
    defer na.deinit();
    var nb = logic.yosys_json.parseModule(gpa, sb, null) catch return fail("parse b json failed");
    defer nb.deinit();
    const r = logic.netlist.combinationalEquiv(gpa, &na, &nb) catch return fail("miter failed");
    defer if (r.cex) |c| gpa.free(c);
    if (r.equivalent) {
        std.debug.print("EQUIVALENT\n", .{});
    } else {
        std.debug.print("NOT_EQUIVALENT\n", .{});
        if (r.cex) |c| {
            for (c, 0..) |v, i| {
                const bit: u8 = if (v == .true_) 1 else 0;
                std.debug.print("  in{d}={d}\n", .{ i, bit });
            }
        }
        std.process.exit(1);
    }
}

/// Tiny term parser: name | name(arg,...,arg)  names are vars if lowercase start else const.
fn parseTerm(pool: *logic.TermPool, src: []const u8) !logic.fol_term.TermId {
    const s = std.mem.trim(u8, src, " \t");
    if (std.mem.indexOfScalar(u8, s, '(')) |lp| {
        const name = s[0..lp];
        if (s[s.len - 1] != ')') return error.Parse;
        const inner = s[lp + 1 .. s.len - 1];
        var args: std.ArrayList(logic.fol_term.TermId) = .empty;
        defer args.deinit(pool.allocator);
        if (inner.len > 0) {
            var depth: i32 = 0;
            var start: usize = 0;
            var i: usize = 0;
            while (i <= inner.len) : (i += 1) {
                const at_end = i == inner.len;
                const c: u8 = if (at_end) ',' else inner[i];
                if (!at_end and c == '(') depth += 1;
                if (!at_end and c == ')') depth -= 1;
                if (at_end or (c == ',' and depth == 0)) {
                    const part = std.mem.trim(u8, inner[start..i], " \t");
                    if (part.len > 0) try args.append(pool.allocator, try parseTerm(pool, part));
                    start = i + 1;
                }
            }
        }
        return try pool.mkFunc(name, args.items);
    }
    if (s.len == 0) return error.Parse;
    if (s[0] >= 'a' and s[0] <= 'z') return try pool.mkVar(s);
    return try pool.mkConst(s);
}

fn cmdIc3Demo(gpa: std.mem.Allocator, frames: u32) !void {
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        var r = try logic.pdr.check(gpa, &nl, q, frames);
        defer r.deinit(gpa);
        std.debug.print("pdr stuck0: {s} frames={d} conflicts={d} gens={d} pushes={d} ctg={d}\n", .{
            @tagName(r.status),
            r.frames,
            r.conflicts,
            r.generalizations,
            r.pushes,
            r.ctg_blocks,
        });
    }
    {
        var nl = logic.Netlist.init(gpa);
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
        var r = try logic.pdr.check(gpa, &nl, bad, frames);
        defer r.deinit(gpa);
        std.debug.print("pdr counter: {s} frames={d} conflicts={d} gens={d} pushes={d} ctg={d}\n", .{
            @tagName(r.status),
            r.frames,
            r.conflicts,
            r.generalizations,
            r.pushes,
            r.ctg_blocks,
        });
    }
}

fn cmdAiger(gpa: std.mem.Allocator, io: std.Io, path: []const u8) !void {
    const src = std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(16 * 1024 * 1024)) catch return fail("read failed");
    defer gpa.free(src);
    var nl = logic.aiger.parse(gpa, src) catch return fail("aiger parse failed");
    defer nl.deinit();
    std.debug.print("AIGER nets={d} inputs={d} outputs={d} gates={d} latches={d} bad={d} constr={d} justice={d} fair={d}\n", .{
        nl.num_nets,
        nl.inputs.items.len,
        nl.outputs.items.len,
        nl.gates.items.len,
        nl.latches.items.len,
        nl.bad.items.len,
        nl.constraints.items.len,
        nl.justice.items.len,
        nl.fairness.items.len,
    });
}

fn cmdAigerWrite(gpa: std.mem.Allocator, io: std.Io, inp: []const u8, outp: []const u8, binary: bool, extended: bool) !void {
    const src = std.Io.Dir.cwd().readFileAlloc(io, inp, gpa, .limited(16 * 1024 * 1024)) catch return fail("read failed");
    defer gpa.free(src);
    var nl = logic.aiger.parse(gpa, src) catch return fail("aiger parse failed");
    defer nl.deinit();
    const bytes = if (binary)
        logic.aiger_write.writeBinary(gpa, &nl) catch return fail("write failed")
    else if (extended)
        logic.aiger_write.write(gpa, &nl, .{ .binary = false, .symbols = true, .extended = true }) catch return fail("write failed")
    else
        logic.aiger_write.writeAsciiSimple(gpa, &nl) catch return fail("write failed");
    defer gpa.free(bytes);
    // write via linux open
    var path_buf: [512]u8 = undefined;
    if (outp.len >= path_buf.len) return fail("path too long");
    @memcpy(path_buf[0..outp.len], outp);
    path_buf[outp.len] = 0;
    const fd = std.os.linux.open(@ptrCast(&path_buf), .{ .ACCMODE = .WRONLY, .CREAT = true, .TRUNC = true }, 0o644);
    if (@as(isize, @bitCast(fd)) < 0) return fail("open out failed");
    _ = std.os.linux.write(@intCast(fd), bytes.ptr, bytes.len);
    _ = std.os.linux.close(@intCast(fd));
    std.debug.print("WROTE {s} bytes={d} binary={} extended={}\n", .{ outp, bytes.len, binary, extended });
}

fn cmdJusticeDemo(gpa: std.mem.Allocator, bound: u32, lasso: bool) !void {
    var nl = logic.Netlist.init(gpa);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addGate(.not, &.{q}, d);
    try nl.addLatch(d, q, false);
    try nl.addOutput(q);
    const r = try logic.justice.check(gpa, &nl, &.{q}, bound, lasso);
    defer if (r.trace) |t| gpa.free(t);
    std.debug.print("justice q bound={d} lasso={}: {s} conflicts={d}\n", .{ bound, lasso, @tagName(r.status), r.conflicts });
}

fn cmdKliveDemo(gpa: std.mem.Allocator, max_k: u32) !void {
    // Stuck-0: infinite proof that justice never holds i.o.
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const r = try logic.kliveness.check(gpa, &nl, &.{q}, max_k, 16, 4);
        std.debug.print("klive stuck0: {s} k={d} conflicts={d}\n", .{ @tagName(r.status), r.k, r.conflicts });
    }
    // Toggle: should find lasso witness, never false-prove
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addGate(.not, &.{q}, d);
        try nl.addLatch(d, q, false);
        const r = try logic.kliveness.check(gpa, &nl, &.{q}, max_k, 12, 4);
        std.debug.print("klive toggle: {s} k={d} conflicts={d}\n", .{ @tagName(r.status), r.k, r.conflicts });
    }
}

fn cmdDoctor(gpa: std.mem.Allocator, io: std.Io) !void {
    std.debug.print("logic-zig doctor\n", .{});
    var fails: u32 = 0;

    // External CaDiCaL (optional)
    if (try logic.external.findSolver(gpa)) |p| {
        defer gpa.free(p);
        std.debug.print("cadical: {s}\n", .{p});
    } else {
        std.debug.print("cadical: UNAVAILABLE (optional)\n", .{});
    }

    // Prop tautology
    {
        var pool = try logic.ExprPool.init(gpa);
        defer pool.deinit();
        if (try logic.isTautology(gpa, &pool, try logic.parse(&pool, "a | !a"))) {
            std.debug.print("ok  prop tautology\n", .{});
        } else {
            std.debug.print("FAIL prop tautology\n", .{});
            fails += 1;
        }
    }
    // CDCL unit conflict
    {
        var cnf = logic.Cnf.init(gpa);
        defer cnf.deinit();
        cnf.ensureVars(1);
        try cnf.addClause(&.{logic.Lit.positive(logic.Var.fromIndex(0))});
        try cnf.addClause(&.{logic.Lit.negative(logic.Var.fromIndex(0))});
        const r = try logic.solveCnf(gpa, &cnf, .{});
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .unsat) {
            std.debug.print("ok  cdcl unsat\n", .{});
        } else {
            std.debug.print("FAIL cdcl unsat\n", .{});
            fails += 1;
        }
    }
    // AIGER extended B/J
    {
        const src =
            \\aag 3 2 0 1 1 1 0 1 0
            \\2
            \\4
            \\6
            \\6 2 4
            \\6
            \\1 2
        ;
        var nl = logic.aiger.parse(gpa, src) catch {
            std.debug.print("FAIL aiger extended parse\n", .{});
            fails += 1;
            std.debug.print("doctor fails={d}\n", .{fails});
            std.process.exit(1);
        };
        defer nl.deinit();
        if (nl.bad.items.len == 1 and nl.justice.items.len == 1) {
            std.debug.print("ok  aiger B/J\n", .{});
        } else {
            std.debug.print("FAIL aiger B/J\n", .{});
            fails += 1;
        }
    }
    // PDR stuck0
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        var r = try logic.pdr.check(gpa, &nl, q, 12);
        defer r.deinit(gpa);
        if (r.status != .violated) {
            std.debug.print("ok  pdr stuck0 {s}\n", .{@tagName(r.status)});
        } else {
            std.debug.print("FAIL pdr stuck0\n", .{});
            fails += 1;
        }
    }
    // k-liveness infinite proof
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const r = try logic.kliveness.proveFiniteHits(gpa, &nl, q, 4, 16);
        if (r.status == .proven_infinite) {
            std.debug.print("ok  klive infinite k={d}\n", .{r.k});
        } else {
            std.debug.print("FAIL klive {s}\n", .{@tagName(r.status)});
            fails += 1;
        }
    }
    // Justice path
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addGate(.not, &.{q}, d);
        try nl.addLatch(d, q, false);
        const r = try logic.justice.check(gpa, &nl, &.{q}, 1, false);
        defer if (r.trace) |t| gpa.free(t);
        if (r.status == .witness) {
            std.debug.print("ok  justice witness\n", .{});
        } else {
            std.debug.print("FAIL justice\n", .{});
            fails += 1;
        }
    }
    // Fair multi-justice
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q0 = try nl.allocNetNamed("q0");
        const q1 = try nl.allocNetNamed("q1");
        const d0 = try nl.allocNetNamed("d0");
        const d1 = try nl.allocNetNamed("d1");
        try nl.addConst(d0, false);
        try nl.addGate(.not, &.{q1}, d1);
        try nl.addLatch(d0, q0, false);
        try nl.addLatch(d1, q1, false);
        const r = try logic.kliveness.check(gpa, &nl, &.{ q0, q1 }, 4, 16, 0);
        if (r.status == .proven_infinite) {
            std.debug.print("ok  fair multi proven\n", .{});
        } else {
            std.debug.print("FAIL fair multi {s}\n", .{@tagName(r.status)});
            fails += 1;
        }
    }
    // Portfolio + RUP
    {
        var cnf = logic.Cnf.init(gpa);
        defer cnf.deinit();
        cnf.ensureVars(1);
        try cnf.addClause(&.{logic.Lit.positive(logic.Var.fromIndex(0))});
        try cnf.addClause(&.{logic.Lit.negative(logic.Var.fromIndex(0))});
        var r = try logic.portfolio.solvePortfolioOpts(gpa, &cnf, .{ .proof_on_unsat = true, .total_conflicts = 50_000 });
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        if (r.status == .unsat) {
            std.debug.print("ok  portfolio unsat\n", .{});
        } else {
            std.debug.print("FAIL portfolio\n", .{});
            fails += 1;
        }
    }
    // DRAT-trim availability (soft)
    {
        if (try logic.drat_external.findDratTrim(gpa)) |p| {
            defer gpa.free(p);
            std.debug.print("ok  drat-trim {s}\n", .{p});
        } else {
            std.debug.print("ok  drat-trim UNAVAILABLE (optional)\n", .{});
        }
    }
    // AIGER write/read
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const a = try nl.allocNetNamed("a");
        const b = try nl.allocNetNamed("b");
        const y = try nl.allocNetNamed("y");
        try nl.addInput(a);
        try nl.addInput(b);
        try nl.addGate(.and_, &.{ a, b }, y);
        try nl.addOutput(y);
        const bytes = try logic.aiger_write.writeAsciiSimple(gpa, &nl);
        defer gpa.free(bytes);
        var nl2 = try logic.aiger.parse(gpa, bytes);
        defer nl2.deinit();
        if (nl2.inputs.items.len == 2) {
            std.debug.print("ok  aiger write/read\n", .{});
        } else {
            std.debug.print("FAIL aiger write/read\n", .{});
            fails += 1;
        }
    }
    // Bench corpus
    {
        const dir = std.Io.Dir.cwd().openDir(io, "corpus/bench/sat", .{ .iterate = true }) catch {
            std.debug.print("bench_corpus: MISSING (optional)\n", .{});
            if (fails != 0) {
                std.debug.print("DOCTOR_FAIL fails={d}\n", .{fails});
                std.process.exit(1);
            }
            std.debug.print("DOCTOR_OK\n", .{});
            return;
        };
        var d = dir;
        defer d.close(io);
        var n: u32 = 0;
        var it = d.iterate();
        while (try it.next(io)) |e| {
            if (e.kind == .file) n += 1;
        }
        std.debug.print("bench_corpus: {d} files\n", .{n});
    }

    if (fails != 0) {
        std.debug.print("DOCTOR_FAIL fails={d}\n", .{fails});
        std.process.exit(1);
    }
    std.debug.print("DOCTOR_OK\n", .{});
}

fn cmdTernaryDemo(gpa: std.mem.Allocator) !void {
    var nl = logic.Netlist.init(gpa);
    defer nl.deinit();
    const a = try nl.allocNetNamed("a");
    const b = try nl.allocNetNamed("b");
    const y = try nl.allocNetNamed("y");
    try nl.addInput(a);
    try nl.addInput(b);
    try nl.addGate(.and_, &.{ a, b }, y);
    var sim = try logic.ternary.SimState.init(gpa, &nl);
    defer sim.deinit();
    sim.set(a, .one);
    sim.set(b, .x);
    sim.evalComb(&nl);
    std.debug.print("ternary 1 & X = {s}\n", .{@tagName(sim.get(y))});
    sim.set(b, .zero);
    sim.evalComb(&nl);
    std.debug.print("ternary 1 & 0 = {s}\n", .{@tagName(sim.get(y))});
}

fn cmdDiffExternal(gpa: std.mem.Allocator, io: std.Io, iters: u32) !void {
    const r = try logic.external.fuzzExternal(gpa, io, 0xCAFE, iters, 8);
    defer if (r.solver) |p| gpa.free(p);
    if (r.unavailable) {
        std.debug.print("EXTERNAL_UNAVAILABLE (build third_party/cadical or set LOGIC_ZIG_EXTERNAL_SOLVER)\n", .{});
        return;
    }
    if (r.solver) |p| std.debug.print("c external_solver={s}\n", .{p});
    if (r.mismatches == 0) {
        std.debug.print("EXTERNAL_DIFF_OK iters={d} mismatches=0\n", .{r.ran});
    } else {
        std.debug.print("EXTERNAL_DIFF_FAIL mismatches={d}/{d}\n", .{ r.mismatches, r.ran });
        std.process.exit(1);
    }
}

fn cmdBenchSuite(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: []const u8,
    timeout_s: f64,
    max_conflicts: u64,
    json: bool,
    fair: bool,
) !void {
    var suite = try logic.bench.runSuiteOpts(gpa, io, dir, timeout_s, max_conflicts, fair);
    defer suite.deinit(gpa);
    if (fair) std.debug.print("c mode=fair_process (sat-track vs cadical subprocess)\n", .{});
    if (json) {
        logic.bench.printJson(&suite);
    } else {
        logic.bench.printSuite(&suite);
    }
    if (suite.mismatches != 0 or suite.model_failures != 0) std.process.exit(1);
    // PAR-2 lose is reported but not a hard fail — correctness is the gate.
}

fn cmdBenchMultishot(
    gpa: std.mem.Allocator,
    io: std.Io,
    nvars: u32,
    queries: u32,
    seed: u64,
) !void {
    const r = try logic.multishot_bench.run(gpa, io, nvars, queries, seed);
    logic.multishot_bench.printResult(&r);
    if (!r.won_throughput and r.external_available) std.process.exit(1);
}

fn cmdCorrectnessSuite(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: []const u8,
    ext_iters: u32,
) !void {
    var rep = try logic.correctness_suite.runAll(gpa, io, dir, ext_iters);
    defer rep.deinit(gpa);
    logic.correctness_suite.printReport(&rep);
    if (!rep.all_pass) std.process.exit(1);
}

fn cmdHwmccBench(gpa: std.mem.Allocator, io: std.Io, frames: u32, dir: []const u8) !void {
    var r = try logic.hwmcc_bench.run(gpa, io, frames, dir);
    defer r.deinit(gpa);
    logic.hwmcc_bench.printResult(&r);
    if (!r.all_ok) std.process.exit(1);
}

fn cmdWinReport(gpa: std.mem.Allocator, io: std.Io, with_comp: bool) !void {
    const r = try logic.win_report.runOpts(gpa, io, with_comp);
    logic.win_report.printScoreboard(&r);
    if (!r.allRequired()) std.process.exit(1);
}

fn cmdBenchComp(
    gpa: std.mem.Allocator,
    io: std.Io,
    dir: []const u8,
    timeout_s: f64,
    max_conflicts: u64,
    check_drat: bool,
) !void {
    var r = try logic.comp_bench.run(gpa, io, dir, timeout_s, max_conflicts, check_drat);
    defer r.deinit(gpa);
    logic.comp_bench.printResult(&r);
    if (!r.correctnessOk()) std.process.exit(1);
}

fn cmdAbduceDemo(gpa: std.mem.Allocator) !void {
    const Lit = logic.lit.Lit;
    const Var = logic.lit.Var;
    const lp = Lit.positive;
    const ln = Lit.negative;
    const v = Var.fromIndex;

    // Diagnosis theory: faultA → s1, faultB → s1, faultB → s2.
    var b = logic.cnf.Cnf.init(gpa);
    defer b.deinit();
    try b.addClause(&.{ ln(v(0)), lp(v(2)) });
    try b.addClause(&.{ ln(v(1)), lp(v(2)) });
    try b.addClause(&.{ ln(v(1)), lp(v(3)) });
    const names = [_][]const u8{ "faultA", "faultB", "s1", "s2" };

    const cases = [_]struct { obs: []const Lit, label: []const u8 }{
        .{ .obs = &.{lp(v(2))}, .label = "s1" },
        .{ .obs = &.{ lp(v(2)), lp(v(3)) }, .label = "s1 & s2" },
    };
    for (cases) |c| {
        var r = try logic.abduction.abduce(gpa, &b, c.obs, &.{ lp(v(0)), lp(v(1)) }, .{});
        defer r.deinit();
        std.debug.print("observe {s}: {d} minimal explanation(s), complete={}\n", .{
            c.label, r.explanations.items.len, r.complete,
        });
        for (r.explanations.items) |e| {
            std.debug.print("  {{", .{});
            for (e, 0..) |l, i| {
                std.debug.print("{s}{s}{s}", .{
                    if (i > 0) ", " else " ",
                    if (l.isNeg()) "!" else "",
                    names[l.variable().index()],
                });
            }
            std.debug.print(" }} verified={}\n", .{
                try logic.abduction.verifyExplanation(gpa, &b, c.obs, e),
            });
        }
    }
}

fn cmdInduceDemo(gpa: std.mem.Allocator) !void {
    // Learn xor(x0, x1) from all four labeled rows.
    const examples = [_]logic.induction.Example{
        .{ .features = &.{ false, false }, .label = false },
        .{ .features = &.{ true, true }, .label = false },
        .{ .features = &.{ true, false }, .label = true },
        .{ .features = &.{ false, true }, .label = true },
    };
    var r = try logic.induction.induceDnf(gpa, 2, &examples, .{});
    defer r.deinit();
    std.debug.print("xor: status={s} k={d} minimal={} verified={}\n", .{
        @tagName(r.status), r.k_used, r.minimal, r.verified,
    });
    for (r.terms) |t| {
        std.debug.print("  term:", .{});
        for (t) |l| std.debug.print(" {s}x{d}", .{ if (l.negated) "!" else "", l.feature });
        std.debug.print("\n", .{});
    }
}

fn cmdReasonDemo(gpa: std.mem.Allocator) !void {
    const Lit = logic.lit.Lit;
    const Var = logic.lit.Var;
    const lp = Lit.positive;
    const ln = Lit.negative;
    const v = Var.fromIndex;

    // 1. Min-cost abduction: a→o (w=5) vs b∧c→o (w=1+1).
    {
        var b = logic.cnf.Cnf.init(gpa);
        defer b.deinit();
        try b.addClause(&.{ ln(v(0)), lp(v(3)) });
        try b.addClause(&.{ ln(v(1)), ln(v(2)), lp(v(3)) });
        const w = [_]u32{ 5, 1, 1 };
        var r = try logic.abduction.abduceMinCost(gpa, &b, &.{lp(v(3))}, &.{ lp(v(0)), lp(v(1)), lp(v(2)) }, .{ .weights = &w });
        defer r.deinit();
        std.debug.print("min-cost abduce: cost={d} optimal={} size={d}\n", .{
            r.cost, r.optimal, if (r.explanation) |e| e.len else 0,
        });
    }
    // 2. ALP: flies(tweety) needs normal(tweety).
    {
        var pool = logic.fol_term.TermPool.init(gpa);
        defer pool.deinit();
        const tweety = try pool.mkConst("tweety");
        const x = try pool.mkVar("X");
        const clauses = [_]logic.alp.Clause{
            .{ .head = try pool.mkFunc("bird", &.{tweety}) },
            .{ .head = try pool.mkFunc("flies", &.{x}), .body = &.{
                try pool.mkFunc("bird", &.{x}),
                try pool.mkFunc("normal", &.{x}),
            } },
        };
        const abd = [_][]const u8{"normal"};
        var r = try logic.alp.abduce(gpa, &pool, .{ .clauses = &clauses, .abducibles = &abd }, &.{
            try pool.mkFunc("flies", &.{tweety}),
        }, .{});
        defer r.deinit();
        std.debug.print("alp: flies(tweety) ← {d} hypothesis set(s), first has {d} atom(s)\n", .{
            r.solutions.items.len,
            if (r.solutions.items.len > 0) r.solutions.items[0].len else 0,
        });
    }
    // 3. Bayesian induction: rule of succession + MAP.
    {
        std.debug.print("bayes: laplace(7 of 10)={d:.4}\n", .{logic.bayes.laplace(7, 10)});
        const ex = [_]logic.bayes.Example{
            .{ .features = &.{ true, true }, .label = true },
            .{ .features = &.{ false, false }, .label = false },
        };
        var post = try logic.bayes.posterior(gpa, 2, &ex, .{ .noise = 0.0 });
        defer post.deinit();
        std.debug.print("bayes: MAP size={d} P(true|{{t,t}})={d:.3}\n", .{
            post.map.size(), post.predict(&.{ true, true }),
        });
    }
    // 4. Default logic: Nixon diamond.
    {
        var w = logic.cnf.Cnf.init(gpa);
        defer w.deinit();
        try w.addClause(&.{lp(v(0))});
        try w.addClause(&.{lp(v(1))});
        const d = [_]logic.default_logic.Default{
            .{ .prereq = &.{lp(v(0))}, .justifications = &.{&.{lp(v(2))}}, .consequent = &.{lp(v(2))} },
            .{ .prereq = &.{lp(v(1))}, .justifications = &.{&.{ln(v(2))}}, .consequent = &.{ln(v(2))} },
        };
        var exts = try logic.default_logic.extensions(gpa, &w, &d, .{});
        defer exts.deinit();
        std.debug.print("default: nixon diamond → {d} extensions\n", .{exts.generating.items.len});
    }
    // 5. KLM rational closure: penguin canon.
    {
        const kb = [_]logic.klm.Conditional{
            .{ .antecedent = &.{lp(v(0))}, .consequent = &.{lp(v(1))} },
            .{ .antecedent = &.{lp(v(2))}, .consequent = &.{ln(v(1))} },
            .{ .antecedent = &.{lp(v(2))}, .consequent = &.{lp(v(0))} },
        };
        var rk = try logic.klm.rank(gpa, null, &kb);
        defer rk.deinit();
        const pf = try logic.klm.query(gpa, null, &kb, &rk, &.{lp(v(2))}, &.{ln(v(1))});
        const rb = try logic.klm.query(gpa, null, &kb, &rk, &.{ lp(v(3)), lp(v(0)) }, &.{lp(v(1))});
        std.debug.print("klm: penguin|~¬fly={} red∧bird|~fly={} levels={d}\n", .{
            pf.entailed, rb.entailed, rk.levels,
        });
    }
}

fn cmdKindDemo(gpa: std.mem.Allocator, max_k: u32) !void {
    // Stuck-at-zero: should PROVEN
    {
        var nl = logic.Netlist.init(gpa);
        defer nl.deinit();
        const q = try nl.allocNetNamed("q");
        const d = try nl.allocNetNamed("d");
        try nl.addConst(d, false);
        try nl.addLatch(d, q, false);
        const r = try logic.kinduction.search(gpa, &nl, q, max_k);
        defer if (r.base.trace) |t| gpa.free(t);
        std.debug.print("stuck0: {s} k={d}\n", .{ @tagName(r.status), r.k });
    }
    // Counter: should VIOLATED
    {
        var nl = logic.Netlist.init(gpa);
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
        const r = try logic.kinduction.search(gpa, &nl, bad, max_k);
        defer if (r.base.trace) |t| gpa.free(t);
        std.debug.print("counter: {s} k={d}\n", .{ @tagName(r.status), r.k });
    }
}

fn cmdBmcDemo(gpa: std.mem.Allocator, bound: u32) !void {
    // 2-bit counter; bad when both bits set.
    var nl = logic.Netlist.init(gpa);
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

    const r = try logic.bmc.check(gpa, &nl, bad, bound);
    defer if (r.trace) |t| gpa.free(t);
    switch (r.status) {
        .safe_up_to_bound => std.debug.print("SAFE_UP_TO_BOUND k={d} conflicts={d}\n", .{ r.bound, r.conflicts }),
        .violated => {
            std.debug.print("VIOLATED k={d} conflicts={d}\n", .{ r.bound, r.conflicts });
            if (r.trace) |tr| {
                var f: u32 = 0;
                while (f <= bound) : (f += 1) {
                    const b0: u8 = if (logic.bmc.traceAt(tr, nl.num_nets, f, q0) == .true_) 1 else 0;
                    const b1: u8 = if (logic.bmc.traceAt(tr, nl.num_nets, f, q1) == .true_) 1 else 0;
                    const bd: u8 = if (logic.bmc.traceAt(tr, nl.num_nets, f, bad) == .true_) 1 else 0;
                    std.debug.print("  t={d} q1q0={d}{d} bad={d}\n", .{ f, b1, b0, bd });
                }
            }
        },
        .unknown => std.debug.print("UNKNOWN\n", .{}),
    }
}

fn cmdUnify(gpa: std.mem.Allocator, t1s: []const u8, t2s: []const u8) !void {
    var pool = logic.TermPool.init(gpa);
    defer pool.deinit();
    const t1 = parseTerm(&pool, t1s) catch return fail("parse term1");
    const t2 = parseTerm(&pool, t2s) catch return fail("parse term2");
    var subst = logic.unify.Subst.init(gpa);
    defer subst.deinit();
    logic.unify.unify(&pool, &subst, t1, t2) catch |e| {
        std.debug.print("UNIFY_FAIL {s}\n", .{@errorName(e)});
        std.process.exit(1);
    };
    std.debug.print("UNIFY_OK\n", .{});
    var it = subst.map.iterator();
    while (it.next()) |e| {
        const vname = pool.nameOf(logic.fol_term.TermId.fromIndex(e.key_ptr.*));
        // value may be var/const/func — print name if leaf
        const val = e.value_ptr.*;
        const vstr = pool.nameOf(val);
        std.debug.print("  {s} |-> {s}\n", .{ vname, vstr });
    }
}

fn cmdUnsat(gpa: std.mem.Allocator, formula: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");
    const q = try logic.satFormula(gpa, &pool, e);
    defer if (q.model) |m| gpa.free(m);
    if (q.status == .unsat) {
        std.debug.print("UNSAT\n", .{});
    } else {
        std.debug.print("SAT\n", .{});
        std.process.exit(1);
    }
}

fn cmdTautology(gpa: std.mem.Allocator, formula: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");
    if (try logic.isTautology(gpa, &pool, e)) {
        std.debug.print("TAUTOLOGY\n", .{});
    } else {
        std.debug.print("NOT_TAUTOLOGY\n", .{});
        std.process.exit(1);
    }
}

fn cmdEquiv(gpa: std.mem.Allocator, f1: []const u8, f2: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const a = logic.parse(&pool, f1) catch return fail("parse error formula1");
    const b = logic.parse(&pool, f2) catch return fail("parse error formula2");
    if (try logic.areEquivalent(gpa, &pool, a, b)) {
        std.debug.print("EQUIVALENT\n", .{});
    } else {
        std.debug.print("NOT_EQUIVALENT\n", .{});
        std.process.exit(1);
    }
}

fn cmdSimplify(gpa: std.mem.Allocator, formula: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");
    const s = try logic.simplify(&pool, e);
    const out = try logic.pretty.toString(gpa, &pool, s);
    defer gpa.free(out);
    std.debug.print("{s}\n", .{out});
}

fn cmdCnf(gpa: std.mem.Allocator, formula: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");
    var tr = try logic.toCnf(&pool, e);
    defer tr.cnf.deinit();

    // Write DIMACS to a buffer then print.
    var aw: std.Io.Writer.Allocating = .init(gpa);
    defer aw.deinit();
    try logic.dimacs.write(&tr.cnf, &aw.writer);
    const s = try aw.toOwnedSlice();
    defer gpa.free(s);
    std.debug.print("{s}", .{s});
}

fn cmdEval(gpa: std.mem.Allocator, formula: []const u8, assign_str: []const u8) !void {
    var pool = try logic.ExprPool.init(gpa);
    defer pool.deinit();
    const e = logic.parse(&pool, formula) catch return fail("parse error");

    var assign = try gpa.alloc(logic.Value, pool.numVars());
    defer gpa.free(assign);
    @memset(assign, .undef);

    var pairs = std.mem.splitScalar(u8, assign_str, ',');
    while (pairs.next()) |pair| {
        const p = std.mem.trim(u8, pair, " \t");
        if (p.len == 0) continue;
        var it = std.mem.splitScalar(u8, p, '=');
        const name = std.mem.trim(u8, it.next() orelse return fail("bad assign"), " \t");
        const val_s = std.mem.trim(u8, it.next() orelse return fail("bad assign"), " \t");

        var found: ?u32 = null;
        var vi: u32 = 0;
        while (vi < pool.numVars()) : (vi += 1) {
            if (std.mem.eql(u8, pool.varName(logic.Var.fromIndex(vi)), name)) {
                found = vi;
                break;
            }
        }
        const idx = found orelse return fail("unknown variable in assign");
        if (std.mem.eql(u8, val_s, "1") or std.mem.eql(u8, val_s, "true")) {
            assign[idx] = .true_;
        } else if (std.mem.eql(u8, val_s, "0") or std.mem.eql(u8, val_s, "false")) {
            assign[idx] = .false_;
        } else return fail("assign values must be 0/1/true/false");
    }

    const v = pool.eval(e, assign);
    const s = switch (v) {
        .true_ => "true",
        .false_ => "false",
        .undef => "undef",
    };
    std.debug.print("{s}\n", .{s});
}
