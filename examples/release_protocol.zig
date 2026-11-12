//! A small release state machine, persisted models, replayable certificate and
//! a checked counterexample after removing the deployment approval guard.
const std = @import("std");
const logic = @import("logic");

const Frame = struct {
    step: u32,
    approved: bool,
    deployed: bool,
    approve_request: bool,
    deploy_request: bool,
    bad: bool,
};

const Outcome = struct {
    allocator: std.mem.Allocator,
    safe_source: []u8,
    unsafe_source: []u8,
    invariant: []u8,
    trace: []Frame,
    bounded_status: logic.bmc.BmcStatus,
    induction_status: logic.kinduction.KindStatus,
    induction_k: u32,
    invariant_verified: bool,
    changed_model_rejected: bool,
    empty_invariant_rejected: bool,
    trace_verified: bool,

    fn deinit(self: *Outcome) void {
        self.allocator.free(self.safe_source);
        self.allocator.free(self.unsafe_source);
        self.allocator.free(self.invariant);
        self.allocator.free(self.trace);
    }

    fn passes(self: *const Outcome) bool {
        return self.bounded_status == .safe_up_to_bound and self.induction_status == .proven and
            self.invariant_verified and self.changed_model_rejected and
            self.empty_invariant_rejected and self.trace_verified and self.trace.len > 1;
    }

    fn writeJson(self: *const Outcome, writer: *std.Io.Writer) !void {
        try std.json.Stringify.value(.{
            .schema_version = @as(u32, 1),
            .status = if (self.passes()) @as([]const u8, "PROTOCOL_DEMO_OK") else "PROTOCOL_DEMO_FAIL",
            .scope = "finite Boolean release model; internal invariant checking and explicit transition replay",
            .safe = .{
                .bounded_status = self.bounded_status,
                .bound = @as(u32, 4),
                .induction_status = self.induction_status,
                .induction_k = self.induction_k,
                .invariant_verified = self.invariant_verified,
                .invariant_origin = "supplied deployed implies approved; checked, not inferred",
            },
            .unsafe = .{
                .first_violation = self.trace.len - 1,
                .trace_verified = self.trace_verified,
                .trace = self.trace,
            },
            .changed_model_rejected = self.changed_model_rejected,
            .empty_invariant_rejected = self.empty_invariant_rejected,
        }, .{ .whitespace = .indent_2 }, writer);
        try writer.writeAll("\n");
    }
};

fn model(allocator: std.mem.Allocator) !logic.Netlist {
    var nl = logic.Netlist.init(allocator);
    errdefer nl.deinit();
    const approve = try nl.allocNetNamed("approve_request");
    const deploy = try nl.allocNetNamed("deploy_request");
    const approved = try nl.allocNetNamed("approved");
    const deployed = try nl.allocNetNamed("deployed");
    const next_approved = try nl.allocNetNamed("next_approved");
    const next_deployed = try nl.allocNetNamed("next_deployed");
    const not_approved = try nl.allocNetNamed("not_approved");
    const bad = try nl.allocNetNamed("deployed_without_approval");
    try nl.addInput(approve);
    try nl.addInput(deploy);
    try nl.addGate(.or_, &.{ approved, approve }, next_approved);
    try nl.addGate(.and_, &.{ deploy, approved }, next_deployed);
    try nl.addGate(.not, &.{approved}, not_approved);
    try nl.addGate(.and_, &.{ deployed, not_approved }, bad);
    try nl.addLatch(next_approved, approved, false);
    try nl.addLatch(next_deployed, deployed, false);
    try nl.addOutput(bad);
    return nl;
}

fn value(trace: []const logic.Value, nl: *const logic.Netlist, step: u32, net: logic.netlist.NetId) !bool {
    return switch (logic.bmc.traceAt(trace, nl.num_nets, step, net)) {
        .true_ => true,
        .false_ => false,
        .undef => error.IncompleteTrace,
    };
}

fn run(allocator: std.mem.Allocator) !Outcome {
    var native = try model(allocator);
    defer native.deinit();
    const safe_source = try logic.aiger_write.write(allocator, &native, .{ .outputs_as_bad = false });
    errdefer allocator.free(safe_source);
    var safe = try logic.aiger.parse(allocator, safe_source);
    defer safe.deinit();
    var changed = try logic.aiger.parse(allocator, safe_source);
    defer changed.deinit();
    // Change only the deployed latch's next-state function. Retain the same
    // combinational graph and property so the saved certificate must be checked
    // against the changed transition, rather than rejected for a different ID.
    changed.latches.items[1].d = changed.inputs.items[1];
    changed.bad.clearRetainingCapacity();
    const unsafe_source = try logic.aiger_write.write(allocator, &changed, .{ .outputs_as_bad = false });
    errdefer allocator.free(unsafe_source);
    var unsafe = try logic.aiger.parse(allocator, unsafe_source);
    defer unsafe.deinit();
    const bad = safe.badProps()[0];
    if (unsafe.badProps()[0] != bad or unsafe.num_nets != safe.num_nets) return error.PropertyMappingChanged;

    const bounded = try logic.bmc.check(allocator, &safe, bad, 4);
    defer if (bounded.trace) |trace| allocator.free(trace);
    const induction = try logic.kinduction.search(allocator, &safe, bad, 4);
    defer if (induction.base.trace) |trace| allocator.free(trace);
    // Supply the reviewable invariant D => A. k-induction is the automatic
    // proof path above; checking this explicit candidate is a separate path.
    const clauses = try allocator.alloc([]logic.Lit, 1);
    clauses[0] = allocator.dupe(logic.Lit, &.{
        logic.Lit.negative(logic.Var.fromIndex(safe.latches.items[1].q.index())),
        logic.Lit.positive(logic.Var.fromIndex(safe.latches.items[0].q.index())),
    }) catch |err| {
        allocator.free(clauses);
        return err;
    };
    var candidate = logic.certificate.InductiveInvariant{
        .allocator = allocator,
        .clauses = clauses,
        .bad = bad,
        .source = .supplied,
    };
    defer candidate.deinit();
    const invariant = try candidate.writeText(allocator);
    errdefer allocator.free(invariant);
    // Reparse exported bytes before checking. The CLI can replay the same pair.
    var replayed = try logic.certificate.InductiveInvariant.parseText(allocator, invariant);
    defer replayed.deinit();
    const invariant_verified = try replayed.verify(allocator, &safe);
    const changed_rejected = !try replayed.verify(allocator, &unsafe);
    var empty = logic.certificate.InductiveInvariant{
        .allocator = allocator,
        .clauses = try allocator.alloc([]logic.Lit, 0),
        .bad = bad,
    };
    defer empty.deinit();
    const empty_rejected = !try empty.verify(allocator, &unsafe);

    const violation = try logic.bmc.check(allocator, &unsafe, bad, 4);
    defer if (violation.trace) |trace| allocator.free(trace);
    if (violation.status != .violated) return error.CounterexampleMissing;
    const witness = violation.trace orelse return error.CounterexampleMissing;
    var frames: std.ArrayList(Frame) = .empty;
    errdefer frames.deinit(allocator);
    for (0..5) |number| {
        const step: u32 = @intCast(number);
        const frame = Frame{
            .step = step,
            .approved = try value(witness, &unsafe, step, unsafe.latches.items[0].q),
            .deployed = try value(witness, &unsafe, step, unsafe.latches.items[1].q),
            .approve_request = try value(witness, &unsafe, step, unsafe.inputs.items[0]),
            .deploy_request = try value(witness, &unsafe, step, unsafe.inputs.items[1]),
            .bad = try value(witness, &unsafe, step, bad),
        };
        try frames.append(allocator, frame);
        if (frame.bad) break;
    }
    var trace_verified = !frames.items[0].approved and !frames.items[0].deployed;
    for (frames.items, 0..) |frame, i| {
        trace_verified = trace_verified and frame.bad == (frame.deployed and !frame.approved);
        if (i > 0) {
            const previous = frames.items[i - 1];
            trace_verified = trace_verified and frame.approved == (previous.approved or previous.approve_request) and
                frame.deployed == previous.deploy_request;
        }
    }
    trace_verified = trace_verified and frames.items[frames.items.len - 1].bad;
    return .{
        .allocator = allocator,
        .safe_source = safe_source,
        .unsafe_source = unsafe_source,
        .invariant = invariant,
        .trace = try frames.toOwnedSlice(allocator),
        .bounded_status = bounded.status,
        .induction_status = induction.status,
        .induction_k = induction.k,
        .invariant_verified = invariant_verified,
        .changed_model_rejected = changed_rejected,
        .empty_invariant_rejected = empty_rejected,
        .trace_verified = trace_verified,
    };
}

pub fn main(init: std.process.Init) !void {
    var args = try std.process.Args.Iterator.initAllocator(init.minimal.args, init.gpa);
    defer args.deinit();
    _ = args.next();
    var out: ?[]const u8 = null;
    if (args.next()) |option| {
        if (!std.mem.eql(u8, option, "--out")) std.process.exit(2);
        out = args.next() orelse std.process.exit(2);
        if (args.next() != null) std.process.exit(2);
    }
    var outcome = try run(init.gpa);
    defer outcome.deinit();
    if (out) |directory| {
        try std.Io.Dir.cwd().createDir(init.io, directory, .default_dir);
        const names = [_][]const u8{ "safe.aag", "unsafe.aag", "safe.invariant.txt" };
        const bodies = [_][]const u8{ outcome.safe_source, outcome.unsafe_source, outcome.invariant };
        for (names, bodies) |name, body| {
            const path = try std.fs.path.join(init.gpa, &.{ directory, name });
            defer init.gpa.free(path);
            try std.Io.Dir.cwd().writeFile(init.io, .{ .sub_path = path, .data = body });
        }
    }
    var buffer: [4096]u8 = undefined;
    var stdout = std.Io.File.stdout().writer(init.io, &buffer);
    try outcome.writeJson(&stdout.interface);
    try stdout.interface.flush();
    if (!outcome.passes()) std.process.exit(1);
}

test "release guard has a replayable invariant and removing it yields a valid trace" {
    var outcome = try run(std.testing.allocator);
    defer outcome.deinit();
    try std.testing.expect(outcome.passes());
    try std.testing.expect(outcome.invariant.len > 0);
    try std.testing.expect(outcome.trace[outcome.trace.len - 1].deployed);
    try std.testing.expect(!outcome.trace[outcome.trace.len - 1].approved);
}
