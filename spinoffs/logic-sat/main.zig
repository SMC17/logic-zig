//! logic-sat — portfolio / DRAT-aware SAT flagship.

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
            \\logic-sat — portfolio CDCL + DRAT (profile=sat-race)
            \\  logic-sat solve <file.cnf>
            \\  logic-sat portfolio <file.cnf> [--proof]
            \\  logic-sat check-drat <file.cnf>
            \\  logic-sat drat-fuzz [--iters N] [--vars V]
            \\  logic-sat hard [--dir DIR] [--limit N] [--conflicts N]
            \\  logic-sat profile
            \\
        , .{});
        return;
    };
    const prof = logic.profiles.get(.sat_race);
    if (std.mem.eql(u8, cmd, "profile")) {
        std.debug.print("profile={s}\n{s}\n", .{ prof.name, prof.blurb });
        if (try logic.drat_external.findDratTrim(gpa)) |p| {
            defer gpa.free(p);
            std.debug.print("drat-trim: {s}\n", .{p});
        } else {
            std.debug.print("drat-trim: UNAVAILABLE\n", .{});
        }
        return;
    }
    if (std.mem.eql(u8, cmd, "drat-fuzz")) {
        var iters: u32 = 30;
        var nvars: u32 = 6;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--iters")) iters = try std.fmt.parseInt(u32, iter.next() orelse "30", 10);
            if (std.mem.eql(u8, a, "--vars")) nvars = try std.fmt.parseInt(u32, iter.next() orelse "6", 10);
        }
        const r = try logic.drat_external.fuzzExternalDrat(gpa, io, 0xD2A7, iters, nvars);
        if (r.unavailable) {
            std.debug.print("DRAT_FUZZ_SKIP unavailable\n", .{});
            return;
        }
        std.debug.print("DRAT_FUZZ ran={d} verified={d} failed={d} skipped={d}\n", .{
            r.ran,
            r.verified,
            r.failed,
            r.skipped,
        });
        if (r.failed != 0) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "hard")) {
        var dir: []const u8 = "corpus/bench/sat";
        var limit: u32 = 12;
        var conflicts: u64 = 200_000;
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--dir")) dir = iter.next() orelse dir;
            if (std.mem.eql(u8, a, "--limit")) limit = try std.fmt.parseInt(u32, iter.next() orelse "12", 10);
            if (std.mem.eql(u8, a, "--conflicts")) conflicts = try std.fmt.parseInt(u64, iter.next() orelse "200000", 10);
        }
        // Prefer sat_hard if present
        if (std.mem.eql(u8, dir, "corpus/bench/sat")) {
            // keep default small suite for speed; user can pass --dir corpus/bench/sat_hard
        }
        var suite = try logic.portfolio_bench.runDir(gpa, io, dir, limit, conflicts);
        logic.portfolio_bench.printSuite(&suite);
        if (suite.failed != 0) std.process.exit(1);
        return;
    }
    if (std.mem.eql(u8, cmd, "solve") or std.mem.eql(u8, cmd, "portfolio") or std.mem.eql(u8, cmd, "check-drat")) {
        const path = iter.next() orelse {
            std.debug.print("missing cnf\n", .{});
            std.process.exit(2);
        };
        var want_proof = std.mem.eql(u8, cmd, "check-drat");
        while (iter.next()) |a| {
            if (std.mem.eql(u8, a, "--proof")) want_proof = true;
        }
        const src = try std.Io.Dir.cwd().readFileAlloc(io, path, gpa, .limited(64 * 1024 * 1024));
        defer gpa.free(src);
        var cnf = try logic.dimacs.parse(gpa, src);
        defer cnf.deinit();

        if (std.mem.eql(u8, cmd, "check-drat")) {
            const r = try logic.drat_external.solveAndCheckExternal(gpa, io, &cnf);
            std.debug.print("s {s}\nc external_drat={s} proof_lines={d}\n", .{
                if (r.status == .sat) "SATISFIABLE" else if (r.status == .unsat) "UNSATISFIABLE" else "UNKNOWN",
                @tagName(r.check),
                r.proof_lines,
            });
            if (r.status == .unsat and r.check == .failed) std.process.exit(1);
            std.process.exit(if (r.status == .sat) 10 else if (r.status == .unsat) 20 else 0);
        }

        if (std.mem.eql(u8, cmd, "portfolio")) {
            var r = try logic.portfolio.solvePortfolioOpts(gpa, &cnf, .{
                .total_conflicts = 2_000_000,
                .proof_on_unsat = want_proof,
                .validate_model = true,
                .ramp = true,
            });
            defer if (r.model) |m| gpa.free(m);
            defer if (r.proof) |*p| {
                var pp = p.*;
                pp.deinit();
            };
            std.debug.print("s {s}\nc config={s} tried={d} conflicts={d} model_valid={}\n", .{
                if (r.status == .sat) "SATISFIABLE" else if (r.status == .unsat) "UNSATISFIABLE" else "UNKNOWN",
                r.config_name,
                r.configs_tried,
                r.conflicts,
                r.model_valid,
            });
            if (r.proof) |*p| {
                const ok = try p.verifyRup(gpa, &cnf);
                std.debug.print("c internal_rup={s}\n", .{if (ok) "ok" else "FAIL"});
                if (want_proof) {
                    const ext = try logic.drat_external.checkProofExternal(gpa, io, &cnf, p);
                    std.debug.print("c external_drat={s}\n", .{@tagName(ext)});
                }
            }
            std.process.exit(if (r.status == .sat) 10 else if (r.status == .unsat) 20 else 0);
        }

        const r = try logic.solveCnf(gpa, &cnf, prof.solver);
        defer if (r.model) |m| gpa.free(m);
        defer if (r.proof) |*p| {
            var pp = p.*;
            pp.deinit();
        };
        std.debug.print("s {s}\nc conflicts={d}\n", .{
            if (r.status == .sat) "SATISFIABLE" else if (r.status == .unsat) "UNSATISFIABLE" else "UNKNOWN",
            r.conflicts,
        });
        std.process.exit(if (r.status == .sat) 10 else if (r.status == .unsat) 20 else 0);
    }
    std.debug.print("unknown: {s}\n", .{cmd});
    std.process.exit(2);
}
