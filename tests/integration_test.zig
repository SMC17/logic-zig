//! Integration tests: parse → CNF → SAT with model validation.

const std = @import("std");
const logic = @import("logic");

test "corpus formulas" {
    const cases = [_]struct {
        formula: []const u8,
        expect_sat: bool,
    }{
        .{ .formula = "a", .expect_sat = true },
        .{ .formula = "a & !a", .expect_sat = false },
        .{ .formula = "a | !a", .expect_sat = true },
        .{ .formula = "(a -> b) & a & !b", .expect_sat = false },
        .{ .formula = "(a | b) & (!a | c) & (!b | !c)", .expect_sat = true },
        .{ .formula = "((P -> Q) & P) -> Q", .expect_sat = true },
        .{ .formula = "a ^ a", .expect_sat = false },
        .{ .formula = "a <-> a", .expect_sat = true },
        .{ .formula = "(a & b) | (a & !b)", .expect_sat = true },
        .{ .formula = "true", .expect_sat = true },
        .{ .formula = "false", .expect_sat = false },
    };

    for (cases) |c| {
        var pool = try logic.ExprPool.init(std.testing.allocator);
        defer pool.deinit();
        const e = try logic.parse(&pool, c.formula);
        const q = try logic.satFormula(std.testing.allocator, &pool, e);
        defer if (q.model) |m| std.testing.allocator.free(m);
        if (c.expect_sat) {
            try std.testing.expect(q.status == .sat);
        } else {
            try std.testing.expect(q.status == .unsat);
        }
    }
}

test "tautology suite" {
    const tauts = [_][]const u8{
        "a | !a",
        "((P -> Q) & P) -> Q",
        "(a -> b) | (b -> a)",
        "a <-> a",
        "!(a & !a)",
    };
    for (tauts) |f| {
        var pool = try logic.ExprPool.init(std.testing.allocator);
        defer pool.deinit();
        const e = try logic.parse(&pool, f);
        try std.testing.expect(try logic.isTautology(std.testing.allocator, &pool, e));
    }

    const not_tauts = [_][]const u8{
        "a",
        "a & b",
        "a -> b",
    };
    for (not_tauts) |f| {
        var pool = try logic.ExprPool.init(std.testing.allocator);
        defer pool.deinit();
        const e = try logic.parse(&pool, f);
        try std.testing.expect(!(try logic.isTautology(std.testing.allocator, &pool, e)));
    }
}

test "dimacs file round path" {
    const src =
        \\p cnf 2 3
        \\1 2 0
        \\-1 0
        \\-2 0
    ;
    var cnf = try logic.dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const r = try logic.solveCnf(std.testing.allocator, &cnf, .{});
    defer if (r.model) |m| std.testing.allocator.free(m);
    try std.testing.expect(r.status == .unsat);
}

test "dimacs sat path" {
    const src =
        \\p cnf 2 2
        \\1 2 0
        \\-1 2 0
    ;
    var cnf = try logic.dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const r = try logic.solveCnf(std.testing.allocator, &cnf, .{});
    try std.testing.expect(r.status == .sat);
    defer std.testing.allocator.free(r.model.?);
    try std.testing.expect(cnf.checkModel(r.model.?));
}

test "semantic equivalence absorption" {
    var pool = try logic.ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const a = try logic.parse(&pool, "(a & b) | (a & !b)");
    const b = try logic.parse(&pool, "a");
    try std.testing.expect(try logic.areEquivalent(std.testing.allocator, &pool, a, b));
}

test "brute force prop check n<=3" {
    // Exhaustive: for all formulas built from 2 vars of limited shape, compare
    // satFormula vs truth table.
    var pool = try logic.ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const formulas = [_][]const u8{
        "a & b",
        "a | b",
        "a -> b",
        "a <-> b",
        "a ^ b",
        "!(a & b)",
        "(a | b) & (!a | !b)",
    };
    for (formulas) |f| {
        // reset pool for clean var ids? same pool reuses a,b — fine
        const e = try logic.parse(&pool, f);
        const n = pool.numVars();
        try std.testing.expect(n >= 2);
        // Use only first 2 vars for brute force of this formula's free vars
        var any = false;
        var bits: u32 = 0;
        while (bits < (@as(u32, 1) << @intCast(n))) : (bits += 1) {
            var assign = try std.testing.allocator.alloc(logic.Value, n);
            defer std.testing.allocator.free(assign);
            var i: u32 = 0;
            while (i < n) : (i += 1) {
                assign[i] = if ((bits >> @intCast(i)) & 1 == 1) .true_ else .false_;
            }
            if (pool.eval(e, assign) == .true_) any = true;
        }
        const q = try logic.satFormula(std.testing.allocator, &pool, e);
        defer if (q.model) |m| std.testing.allocator.free(m);
        if (any) {
            try std.testing.expect(q.status == .sat);
        } else {
            try std.testing.expect(q.status == .unsat);
        }
    }
}

test "producer serialized proof passes independent checker" {
    const src = "p cnf 2 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
    var cnf = try logic.dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    var result = try logic.solveCnf(std.testing.allocator, &cnf, .{ .proof = true });
    defer if (result.proof) |*proof| proof.deinit();
    try std.testing.expectEqual(logic.SolveStatus.unsat, result.status);
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();
    try result.proof.?.writeDimacsLike(&output.writer);
    const serialized = try output.toOwnedSlice();
    defer std.testing.allocator.free(serialized);
    try std.testing.expectEqual(logic.rup_checker.CheckStatus.verified, try logic.rup_checker.verify(std.testing.allocator, src, serialized));
}

test "producer assumption proof preserves serialized context" {
    const src = "p cnf 1 1\n1 0\n";
    var cnf = try logic.dimacs.parse(std.testing.allocator, src);
    defer cnf.deinit();
    const not_a = logic.Lit.negative(logic.Var.fromIndex(0));
    var solver = try logic.Solver.init(std.testing.allocator, &cnf, .{ .proof = true });
    defer solver.deinit();
    var result = try solver.solveAssumptions(&.{not_a});
    defer if (result.assumption_core) |core| std.testing.allocator.free(core);
    defer if (result.proof) |*proof| proof.deinit();
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();
    try result.proof.?.writeDimacsLike(&output.writer);
    const serialized = try output.toOwnedSlice();
    defer std.testing.allocator.free(serialized);
    try std.testing.expectEqual(logic.rup_checker.CheckStatus.verified, try logic.rup_checker.verify(std.testing.allocator, src, serialized));
}
