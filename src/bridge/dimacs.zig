//! DIMACS CNF parser and writer.

const std = @import("std");
const cnf_mod = @import("../sat/cnf.zig");
const lit_mod = @import("../core/lit.zig");

const Cnf = cnf_mod.Cnf;
const Lit = lit_mod.Lit;

pub const DimacsError = error{
    InvalidFormat,
    UnexpectedEof,
    InvalidCharacter,
    Overflow,
    TooManyVars,
    TooManyClauses,
} || std.mem.Allocator.Error;

/// Hard caps for competition robustness (OOM / DoS prevention on untrusted CNF).
pub const MAX_DECLARED_VARS: u32 = 50_000_000;
pub const MAX_DECLARED_CLAUSES: u64 = 200_000_000;
pub const MAX_CLAUSE_LITS: u32 = 1_000_000;

pub fn parse(allocator: std.mem.Allocator, source: []const u8) DimacsError!Cnf {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();

    // Empty / whitespace-only → empty formula (SAT).
    const trimmed_all = std.mem.trim(u8, source, " \t\r\n");
    if (trimmed_all.len == 0) return cnf;

    var declared_vars: ?u32 = null;
    var declared_clauses: ?u64 = null;
    var clause_buf: std.ArrayList(Lit) = .empty;
    defer clause_buf.deinit(allocator);
    var saw_clause_data = false;

    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");
        if (line.len == 0) continue;
        if (line[0] == 'c' or line[0] == '%') continue; // comments + SAT competition section end
        if (line[0] == 'p') {
            // p cnf <vars> <clauses>
            var it = std.mem.tokenizeAny(u8, line, " \t");
            _ = it.next(); // p
            const kind = it.next() orelse return error.InvalidFormat;
            if (!std.mem.eql(u8, kind, "cnf")) return error.InvalidFormat;
            const vs = it.next() orelse return error.InvalidFormat;
            const cs = it.next() orelse return error.InvalidFormat;
            const nv = std.fmt.parseInt(u32, vs, 10) catch return error.InvalidFormat;
            const nc = std.fmt.parseInt(u64, cs, 10) catch return error.InvalidFormat;
            if (nv > MAX_DECLARED_VARS) return error.TooManyVars;
            if (nc > MAX_DECLARED_CLAUSES) return error.TooManyClauses;
            declared_vars = nv;
            declared_clauses = nc;
            cnf.ensureVars(nv);
            continue;
        }

        // Reject garbage lines that are not numbers / clauses (competition harden).
        // Allow leading '+' for some generators; skip pure comment-like junk already handled.
        if (line[0] != '-' and line[0] != '+' and (line[0] < '0' or line[0] > '9')) {
            // Soft-skip unknown section markers used by some competition dumps
            if (line[0] == 's' or line[0] == 'v' or line[0] == 'd') continue;
            return error.InvalidFormat;
        }

        saw_clause_data = true;
        var it = std.mem.tokenizeAny(u8, line, " \t");
        while (it.next()) |tok| {
            if (tok.len == 0) continue;
            const n = std.fmt.parseInt(i32, tok, 10) catch return error.InvalidFormat;
            if (n == 0) {
                try cnf.addClause(clause_buf.items);
                clause_buf.clearRetainingCapacity();
            } else {
                if (clause_buf.items.len >= MAX_CLAUSE_LITS) return error.Overflow;
                // Reject lit 0 already handled; reject absurd var indices
                const abs_n: u32 = if (n < 0) @intCast(-n) else @intCast(n);
                if (abs_n > MAX_DECLARED_VARS) return error.TooManyVars;
                const lit = Lit.fromDimacs(n);
                const need = lit.variable().index() + 1;
                cnf.ensureVars(need);
                try clause_buf.append(allocator, lit);
            }
        }
    }
    if (clause_buf.items.len != 0) {
        // Incomplete clause without trailing 0 — accept as clause for robustness.
        try cnf.addClause(clause_buf.items);
    }
    return cnf;
}

pub fn write(cnf: *const Cnf, writer: *std.Io.Writer) !void {
    try writer.print("p cnf {d} {d}\n", .{ cnf.num_vars, cnf.numClauses() });
    for (0..cnf.numClauses()) |ci| {
        const cl = cnf.clauseSlice(cnf_mod.ClauseId.fromIndex(@intCast(ci)));
        for (cl) |l| {
            try writer.print("{d} ", .{l.toDimacs()});
        }
        try writer.writeAll("0\n");
    }
}

test "dimacs parse" {
    const src =
        \\c comment
        \\p cnf 3 2
        \\1 -2 0
        \\3 0
    ;
    var cnf = try parse(std.testing.allocator, src);
    defer cnf.deinit();
    try std.testing.expect(cnf.num_vars == 3);
    try std.testing.expect(cnf.numClauses() == 2);
}

test "dimacs rejects garbage" {
    try std.testing.expectError(error.InvalidFormat, parse(std.testing.allocator, "hello world\n"));
}

test "dimacs empty is sat formula" {
    var cnf = try parse(std.testing.allocator, "");
    defer cnf.deinit();
    try std.testing.expect(cnf.numClauses() == 0);
}

test "dimacs rejects absurd var declaration" {
    try std.testing.expectError(error.TooManyVars, parse(std.testing.allocator, "p cnf 999999999 1\n"));
}
