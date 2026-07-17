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
} || std.mem.Allocator.Error;

pub fn parse(allocator: std.mem.Allocator, source: []const u8) DimacsError!Cnf {
    var cnf = Cnf.init(allocator);
    errdefer cnf.deinit();

    var declared_vars: ?u32 = null;
    var clause_buf: std.ArrayList(Lit) = .empty;
    defer clause_buf.deinit(allocator);

    var lines = std.mem.splitScalar(u8, source, '\n');
    while (lines.next()) |raw_line| {
        const line = std.mem.trim(u8, raw_line, " \t\r");
        if (line.len == 0) continue;
        if (line[0] == 'c') continue;
        if (line[0] == 'p') {
            // p cnf <vars> <clauses>
            var it = std.mem.tokenizeAny(u8, line, " \t");
            _ = it.next(); // p
            const kind = it.next() orelse return error.InvalidFormat;
            if (!std.mem.eql(u8, kind, "cnf")) return error.InvalidFormat;
            const vs = it.next() orelse return error.InvalidFormat;
            const cs = it.next() orelse return error.InvalidFormat;
            declared_vars = try std.fmt.parseInt(u32, vs, 10);
            _ = cs;
            cnf.ensureVars(declared_vars.?);
            continue;
        }

        var it = std.mem.tokenizeAny(u8, line, " \t");
        while (it.next()) |tok| {
            if (tok.len == 0) continue;
            const n = std.fmt.parseInt(i32, tok, 10) catch return error.InvalidFormat;
            if (n == 0) {
                try cnf.addClause(clause_buf.items);
                clause_buf.clearRetainingCapacity();
            } else {
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
