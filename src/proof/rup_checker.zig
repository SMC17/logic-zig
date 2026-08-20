//! Producer-independent serialized RUP checker.
//!
//! This module imports only `std`: no CDCL solver, preprocessing, producer proof
//! object, or mutable producer IR. It checks strict DIMACS CNF plus a line-based
//! proof format:
//!
//!   a <assumption literals> 0   (optional, first non-comment proof line)
//!   <RUP clause> 0
//!   d <existing clause> 0
//!
//! The last line must add the empty clause.

const std = @import("std");

pub const CheckStatus = enum { verified, invalid };

const ParsedCnf = struct {
    allocator: std.mem.Allocator,
    num_vars: u32,
    clauses: std.ArrayList([]i32) = .empty,

    fn deinit(self: *ParsedCnf) void {
        for (self.clauses.items) |clause| self.allocator.free(clause);
        self.clauses.deinit(self.allocator);
    }
};

fn parseLiteral(token: []const u8) !i32 {
    const wide = std.fmt.parseInt(i64, token, 10) catch return error.InvalidInteger;
    if (wide < std.math.minInt(i32) or wide > std.math.maxInt(i32)) return error.IntegerOverflow;
    return @intCast(wide);
}

fn absVar(lit: i32) !u32 {
    if (lit == std.math.minInt(i32)) return error.IntegerOverflow;
    return @intCast(if (lit < 0) -lit else lit);
}

fn parseCnf(allocator: std.mem.Allocator, text: []const u8) !ParsedCnf {
    var parsed = ParsedCnf{ .allocator = allocator, .num_vars = 0 };
    errdefer parsed.deinit();
    var header_seen = false;
    var declared_clauses: u32 = 0;
    var current: std.ArrayList(i32) = .empty;
    defer current.deinit(allocator);

    var lines = std.mem.splitScalar(u8, text, '\n');
    while (lines.next()) |raw| {
        const line = std.mem.trim(u8, raw, " \t\r");
        if (line.len == 0 or line[0] == 'c') continue;
        if (line[0] == 'p') {
            if (header_seen or current.items.len != 0) return error.InvalidHeader;
            var fields = std.mem.tokenizeAny(u8, line, " \t\r");
            if (!std.mem.eql(u8, fields.next() orelse return error.InvalidHeader, "p")) return error.InvalidHeader;
            if (!std.mem.eql(u8, fields.next() orelse return error.InvalidHeader, "cnf")) return error.InvalidHeader;
            parsed.num_vars = std.fmt.parseInt(u32, fields.next() orelse return error.InvalidHeader, 10) catch return error.InvalidHeader;
            declared_clauses = std.fmt.parseInt(u32, fields.next() orelse return error.InvalidHeader, 10) catch return error.InvalidHeader;
            if (fields.next() != null) return error.InvalidHeader;
            header_seen = true;
            continue;
        }
        if (!header_seen) return error.MissingHeader;
        var tokens = std.mem.tokenizeAny(u8, line, " \t\r");
        while (tokens.next()) |token| {
            const lit = try parseLiteral(token);
            if (lit == 0) {
                try parsed.clauses.append(allocator, try allocator.dupe(i32, current.items));
                current.clearRetainingCapacity();
            } else {
                const variable = try absVar(lit);
                if (variable == 0 or variable > parsed.num_vars) return error.VariableOutOfRange;
                try current.append(allocator, lit);
            }
        }
    }
    if (!header_seen) return error.MissingHeader;
    if (current.items.len != 0) return error.UnterminatedClause;
    if (parsed.clauses.items.len != declared_clauses) return error.ClauseCountMismatch;
    return parsed;
}

fn parseProofClause(allocator: std.mem.Allocator, text: []const u8, num_vars: u32) ![]i32 {
    var clause: std.ArrayList(i32) = .empty;
    errdefer clause.deinit(allocator);
    var terminated = false;
    var tokens = std.mem.tokenizeAny(u8, text, " \t\r");
    while (tokens.next()) |token| {
        const lit = try parseLiteral(token);
        if (terminated) return error.TrailingProofData;
        if (lit == 0) {
            terminated = true;
        } else {
            const variable = try absVar(lit);
            if (variable == 0 or variable > num_vars) return error.VariableOutOfRange;
            try clause.append(allocator, lit);
        }
    }
    if (!terminated) return error.UnterminatedClause;
    return try clause.toOwnedSlice(allocator);
}

fn sameClause(allocator: std.mem.Allocator, left: []const i32, right: []const i32) !bool {
    if (left.len != right.len) return false;
    const used = try allocator.alloc(bool, right.len);
    defer allocator.free(used);
    @memset(used, false);
    for (left) |lit| {
        var found = false;
        for (right, 0..) |candidate, index| {
            if (!used[index] and lit == candidate) {
                used[index] = true;
                found = true;
                break;
            }
        }
        if (!found) return false;
    }
    return true;
}

fn isRup(allocator: std.mem.Allocator, clauses: []const []const i32, num_vars: u32, candidate: []const i32) !bool {
    const assignment = try allocator.alloc(i8, num_vars + 1);
    defer allocator.free(assignment);
    @memset(assignment, 0);

    for (candidate) |lit| {
        const variable = try absVar(lit);
        const value: i8 = if (lit < 0) 1 else -1;
        if (assignment[variable] != 0 and assignment[variable] != value) return true;
        assignment[variable] = value;
    }

    var changed = true;
    while (changed) {
        changed = false;
        for (clauses) |clause| {
            var satisfied = false;
            var unassigned: u32 = 0;
            var unit: i32 = 0;
            for (clause) |lit| {
                const variable = try absVar(lit);
                const value = assignment[variable];
                if ((lit > 0 and value == 1) or (lit < 0 and value == -1)) {
                    satisfied = true;
                    break;
                }
                if (value == 0) {
                    unassigned += 1;
                    unit = lit;
                }
            }
            if (satisfied) continue;
            if (unassigned == 0) return true;
            if (unassigned == 1) {
                const variable = try absVar(unit);
                const value: i8 = if (unit > 0) 1 else -1;
                if (assignment[variable] != 0 and assignment[variable] != value) return true;
                if (assignment[variable] == 0) {
                    assignment[variable] = value;
                    changed = true;
                }
            }
        }
    }
    return false;
}

pub fn verify(allocator: std.mem.Allocator, cnf_text: []const u8, proof_text: []const u8) !CheckStatus {
    var cnf = try parseCnf(allocator, cnf_text);
    defer cnf.deinit();
    var live: std.ArrayList([]i32) = .empty;
    defer {
        for (live.items) |clause| allocator.free(clause);
        live.deinit(allocator);
    }
    for (cnf.clauses.items) |clause| try live.append(allocator, try allocator.dupe(i32, clause));

    var saw_proof_line = false;
    var saw_assumptions = false;
    var final_empty_add = false;
    var lines = std.mem.splitScalar(u8, proof_text, '\n');
    while (lines.next()) |raw| {
        var line = std.mem.trim(u8, raw, " \t\r");
        if (line.len == 0 or line[0] == 'c') continue;
        var kind: enum { add, del, assumptions } = .add;
        if (line[0] == 'd' and (line.len == 1 or std.ascii.isWhitespace(line[1]))) {
            kind = .del;
            line = std.mem.trim(u8, line[1..], " \t\r");
        } else if (line[0] == 'a' and (line.len == 1 or std.ascii.isWhitespace(line[1]))) {
            kind = .assumptions;
            line = std.mem.trim(u8, line[1..], " \t\r");
        }
        const clause = try parseProofClause(allocator, line, cnf.num_vars);
        defer allocator.free(clause);
        if (kind == .assumptions) {
            if (saw_proof_line or saw_assumptions) return error.InvalidAssumptionContext;
            saw_assumptions = true;
            for (clause) |assumption| try live.append(allocator, try allocator.dupe(i32, &.{assumption}));
            continue;
        }
        saw_proof_line = true;
        final_empty_add = false;
        if (kind == .del) {
            var found: ?usize = null;
            for (live.items, 0..) |existing, index| {
                if (try sameClause(allocator, existing, clause)) {
                    found = index;
                    break;
                }
            }
            if (found == null) return .invalid;
            allocator.free(live.items[found.?]);
            _ = live.orderedRemove(found.?);
        } else {
            if (!try isRup(allocator, live.items, cnf.num_vars, clause)) return .invalid;
            try live.append(allocator, try allocator.dupe(i32, clause));
            final_empty_add = clause.len == 0;
        }
    }
    if (!saw_proof_line or !final_empty_add) return .invalid;
    return .verified;
}

test "serialized checker verifies assumptions and rejects their removal" {
    const cnf = "p cnf 1 1\n1 0\n";
    try std.testing.expectEqual(CheckStatus.verified, try verify(std.testing.allocator, cnf, "a -1 0\n0\n"));
    try std.testing.expectEqual(CheckStatus.invalid, try verify(std.testing.allocator, cnf, "0\n"));
}

test "serialized checker rejects mutated proof and unknown deletion" {
    const trivial = "p cnf 2 2\n1 0\n-1 0\n";
    try std.testing.expectEqual(CheckStatus.verified, try verify(std.testing.allocator, trivial, "0\n"));
    const parity = "p cnf 3 4\n1 2 0\n1 -2 0\n-1 2 0\n-1 -2 0\n";
    try std.testing.expectEqual(CheckStatus.invalid, try verify(std.testing.allocator, parity, "3 0\n0\n"));
    try std.testing.expectEqual(CheckStatus.invalid, try verify(std.testing.allocator, parity, "d 3 0\n0\n"));
}

test "serialized checker parses strict DIMACS" {
    try std.testing.expectError(error.ClauseCountMismatch, verify(std.testing.allocator, "p cnf 1 2\n1 0\n", "0\n"));
    try std.testing.expectError(error.VariableOutOfRange, verify(std.testing.allocator, "p cnf 1 1\n2 0\n", "0\n"));
    try std.testing.expectError(error.UnterminatedClause, verify(std.testing.allocator, "p cnf 1 1\n1\n", "0\n"));
}
