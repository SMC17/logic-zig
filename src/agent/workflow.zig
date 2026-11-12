//! Named, data-driven assumption queries over one reusable SAT session.
//! Models and cores are checked against the original clauses and assumptions.
const std = @import("std");
const session_mod = @import("session.zig");
const cnf_mod = @import("../sat/cnf.zig");
const solver = @import("../sat/solver.zig");
const lit = @import("../core/lit.zig");

pub const Input = struct {
    schema_version: u32,
    title: []const u8 = "Reasoning workflow",
    variables: []const []const u8,
    clauses: []const []const []const u8,
    queries: []const Query,
    max_conflicts: u64 = 200_000,

    pub const Query = struct {
        id: []const u8,
        assumptions: []const []const u8 = &.{},
    };
};

pub const Assignment = struct { variable: []const u8, value: bool };

pub const QueryOutput = struct {
    id: []const u8,
    status: solver.SolveStatus,
    model: ?[]Assignment = null,
    model_verified: bool = false,
    core: ?[][]const u8 = null,
    core_verified: bool = false,
    core_deletion_minimal: bool = false,
    conflicts: u64,

    fn deinit(self: *QueryOutput, allocator: std.mem.Allocator) void {
        if (self.model) |model| allocator.free(model);
        if (self.core) |core| allocator.free(core);
    }
};

pub const Report = struct {
    allocator: std.mem.Allocator,
    parsed: std.json.Parsed(Input),
    results: []QueryOutput,
    complete: bool,
    input_sha256: [64]u8,

    pub fn deinit(self: *Report) void {
        for (self.results) |*result| result.deinit(self.allocator);
        self.allocator.free(self.results);
        self.parsed.deinit();
        self.* = undefined;
    }

    pub fn writeJson(self: *const Report, writer: *std.Io.Writer) !void {
        try std.json.Stringify.value(.{
            .schema_version = @as(u32, 1),
            .kind = "assumption_workflow",
            .title = self.parsed.value.title,
            .status = if (self.complete) @as([]const u8, "WORKFLOW_OK") else "WORKFLOW_INCOMPLETE",
            .complete = self.complete,
            .input_sha256 = self.input_sha256[0..],
            .scope = "encoded constraints; internal model/core rechecks; no independent UNSAT proof or action authorization",
            .variables = self.parsed.value.variables,
            .results = self.results,
        }, .{ .whitespace = .indent_2 }, writer);
        try writer.writeAll("\n");
    }
};

fn parseLiteral(names: *const std.StringHashMap(u32), text: []const u8) !lit.Lit {
    if (text.len == 0) return error.EmptyLiteral;
    const negative = text[0] == '!';
    const name = if (negative) text[1..] else text;
    const index = names.get(name) orelse return error.UnknownVariable;
    return lit.Lit.make(lit.Var.fromIndex(index), negative);
}

fn parseLiterals(allocator: std.mem.Allocator, names: *const std.StringHashMap(u32), texts: []const []const u8) ![]lit.Lit {
    const result = try allocator.alloc(lit.Lit, texts.len);
    errdefer allocator.free(result);
    for (texts, 0..) |text, i| result[i] = try parseLiteral(names, text);
    return result;
}

/// A separate solve of the original clauses plus unit assumptions. No learned
/// clauses or mutable trail from the multishot session are reused in this check.
fn recheck(allocator: std.mem.Allocator, formula: *const cnf_mod.Cnf, assumptions: []const lit.Lit, budget: u64) !solver.SolveStatus {
    var cnf = cnf_mod.Cnf.init(allocator);
    defer cnf.deinit();
    cnf.ensureVars(formula.num_vars);
    for (0..formula.numClauses()) |i| try cnf.addClause(formula.clauseSlice(cnf_mod.ClauseId.fromIndex(@intCast(i))));
    for (assumptions) |assumption| try cnf.addClause(&.{assumption});
    const result = try solver.solveCnf(allocator, &cnf, .{ .max_conflicts = budget });
    defer if (result.model) |model| allocator.free(model);
    defer if (result.proof) |*proof| {
        var owned = proof.*;
        owned.deinit();
    };
    return result.status;
}

/// Owns the parsed input and output allocations until Report.deinit().
pub fn run(allocator: std.mem.Allocator, source: []const u8) !Report {
    var parsed = try std.json.parseFromSlice(Input, allocator, source, .{ .allocate = .alloc_always });
    errdefer parsed.deinit();
    const input = parsed.value;
    if (input.schema_version != 1) return error.UnsupportedSchema;
    if (input.variables.len > std.math.maxInt(i32)) return error.TooManyVariables;
    if (input.queries.len == 0) return error.NoQueries;

    var names = std.StringHashMap(u32).init(allocator);
    defer names.deinit();
    for (input.variables, 0..) |name, i| {
        if (name.len == 0 or name[0] == '!') return error.InvalidVariableName;
        const entry = try names.getOrPut(name);
        if (entry.found_existing) return error.DuplicateVariable;
        entry.value_ptr.* = @intCast(i);
    }
    var ids = std.StringHashMap(void).init(allocator);
    defer ids.deinit();
    // Validate every query before executing any, including trailing requests.
    for (input.queries) |query| {
        if (query.id.len == 0) return error.EmptyQueryId;
        const entry = try ids.getOrPut(query.id);
        if (entry.found_existing) return error.DuplicateQueryId;
        for (query.assumptions, 0..) |text, i| {
            _ = try parseLiteral(&names, text);
            for (query.assumptions[0..i]) |previous| {
                if (std.mem.eql(u8, previous, text)) return error.DuplicateAssumption;
            }
        }
    }

    var session = session_mod.Session.init(allocator);
    defer session.deinit();
    session.opts.max_conflicts = input.max_conflicts;
    session.ensureVars(@intCast(input.variables.len));
    for (input.clauses) |clause| {
        const literals = try parseLiterals(allocator, &names, clause);
        defer allocator.free(literals);
        try session.addClause(literals);
    }

    var outputs: std.ArrayList(QueryOutput) = .empty;
    errdefer {
        for (outputs.items) |*result| result.deinit(allocator);
        outputs.deinit(allocator);
    }
    var complete = true;
    for (input.queries) |query| {
        const assumptions = try parseLiterals(allocator, &names, query.assumptions);
        defer allocator.free(assumptions);
        var result = try session.query(assumptions);
        defer result.deinit(allocator);
        var output: QueryOutput = .{ .id = query.id, .status = result.status, .conflicts = result.conflicts };
        errdefer output.deinit(allocator);
        switch (result.status) {
            .sat => {
                const model = result.model orelse return error.MissingModel;
                if (model.len < input.variables.len or !session.formula.checkModel(model)) return error.InvalidModel;
                for (assumptions) |assumption| {
                    if (lit.evalLit(assumption, model) != .true_) return error.InvalidModel;
                }
                output.model = try allocator.alloc(Assignment, input.variables.len);
                for (input.variables, 0..) |name, i| {
                    if (model[i] == .undef) return error.IncompleteModel;
                    output.model.?[i] = .{ .variable = name, .value = model[i] == .true_ };
                }
                output.model_verified = true;
            },
            .unsat => {
                const core = result.core orelse &.{};
                if (result.core == null and assumptions.len > 0) return error.MissingCore;
                output.core = try allocator.alloc([]const u8, core.len);
                const core_lits = try allocator.alloc(lit.Lit, core.len);
                defer allocator.free(core_lits);
                for (core, 0..) |dimension, i| {
                    var found = false;
                    for (assumptions, query.assumptions) |assumption, text| {
                        if (assumption.toDimacs() == dimension) {
                            core_lits[i] = assumption;
                            output.core.?[i] = text;
                            found = true;
                            break;
                        }
                    }
                    if (!found) return error.CoreNotSubset;
                }
                output.core_verified = try recheck(allocator, &session.formula, core_lits, input.max_conflicts) == .unsat;
                output.core_deletion_minimal = output.core_verified;
                for (0..core_lits.len) |drop| {
                    var reduced: std.ArrayList(lit.Lit) = .empty;
                    defer reduced.deinit(allocator);
                    for (core_lits, 0..) |assumption, i| if (i != drop) try reduced.append(allocator, assumption);
                    if (try recheck(allocator, &session.formula, reduced.items, input.max_conflicts) != .sat) {
                        output.core_deletion_minimal = false;
                        break;
                    }
                }
                if (!output.core_verified) complete = false;
            },
            .unknown => complete = false,
        }
        try outputs.append(allocator, output);
    }
    var digest: [32]u8 = undefined;
    std.crypto.hash.sha2.Sha256.hash(source, &digest, .{});
    return .{
        .allocator = allocator,
        .parsed = parsed,
        .results = try outputs.toOwnedSlice(allocator),
        .complete = complete,
        .input_sha256 = std.fmt.bytesToHex(digest, .lower),
    };
}

test "workflow checks models and explains contradictory assumptions across requests" {
    const source =
        \\{"schema_version":1,"variables":["deploy","approved"],
        \\"clauses":[["!deploy","approved"]],"queries":[
        \\{"id":"blocked","assumptions":["deploy","!approved"]},
        \\{"id":"permitted","assumptions":["deploy","approved"]}]}
    ;
    var report = try run(std.testing.allocator, source);
    defer report.deinit();
    try std.testing.expect(report.complete);
    try std.testing.expectEqual(solver.SolveStatus.unsat, report.results[0].status);
    try std.testing.expect(report.results[0].core_verified and report.results[0].core_deletion_minimal);
    try std.testing.expectEqual(@as(usize, 2), report.results[0].core.?.len);
    try std.testing.expect(report.results[1].model_verified);
    try std.testing.expectEqual(solver.SolveStatus.sat, report.results[1].status);
}

test "workflow rejects invalid names, schemas and requests before solving" {
    const cases = .{
        .{ error.UnsupportedSchema, "{\"schema_version\":2,\"variables\":[],\"clauses\":[],\"queries\":[{\"id\":\"q\"}]}" },
        .{ error.NoQueries, "{\"schema_version\":1,\"variables\":[],\"clauses\":[],\"queries\":[]}" },
        .{ error.DuplicateVariable, "{\"schema_version\":1,\"variables\":[\"a\",\"a\"],\"clauses\":[],\"queries\":[{\"id\":\"q\"}]}" },
        .{ error.UnknownVariable, "{\"schema_version\":1,\"variables\":[\"a\"],\"clauses\":[],\"queries\":[{\"id\":\"q\",\"assumptions\":[\"b\"]}]}" },
        .{ error.DuplicateQueryId, "{\"schema_version\":1,\"variables\":[],\"clauses\":[],\"queries\":[{\"id\":\"q\"},{\"id\":\"q\"}]}" },
        .{ error.DuplicateAssumption, "{\"schema_version\":1,\"variables\":[\"a\"],\"clauses\":[],\"queries\":[{\"id\":\"q\",\"assumptions\":[\"a\",\"a\"]}]}" },
    };
    inline for (cases) |case| try std.testing.expectError(case[0], run(std.testing.allocator, case[1]));
}

test "workflow preserves unknown under a zero budget" {
    var report = try run(std.testing.allocator,
        \\{"schema_version":1,"variables":["a"],"clauses":[],"max_conflicts":0,"queries":[{"id":"q"}]}
    );
    defer report.deinit();
    try std.testing.expect(!report.complete);
    try std.testing.expectEqual(solver.SolveStatus.unknown, report.results[0].status);
    try std.testing.expect(report.results[0].model == null);
}

test "workflow owns its input and handles a globally contradictory base" {
    const source = try std.testing.allocator.dupe(u8,
        \\{"schema_version":1,"variables":[],"clauses":[[]],"queries":[{"id":"inconsistent_base"}]}
    );
    var report = run(std.testing.allocator, source) catch |err| {
        std.testing.allocator.free(source);
        return err;
    };
    std.testing.allocator.free(source);
    defer report.deinit();
    try std.testing.expect(report.complete);
    try std.testing.expect(report.results[0].core_verified);
    try std.testing.expectEqual(@as(usize, 0), report.results[0].core.?.len);
    var output: std.Io.Writer.Allocating = .init(std.testing.allocator);
    defer output.deinit();
    try report.writeJson(&output.writer);
    try std.testing.expect(std.mem.indexOf(u8, output.written(), "inconsistent_base") != null);
}
