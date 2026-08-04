//! Serialized forcing traces for modal certificates.
//!
//! A trace is a linear log of recursive forcing judgments
//!   (world, formula_tag, result)
//! produced while evaluating a formula under a fixed frame/valuation.
//! Used to attach human-auditable evidence to countermodel certs.

const std = @import("std");
const normal = @import("normal.zig");

pub const Step = struct {
    world: u32,
    tag: u8, // matches formula tag encoding
    result: bool,
};

pub const Trace = struct {
    steps: []Step,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *Trace) void {
        self.allocator.free(self.steps);
        self.* = undefined;
    }
};

fn tagOf(phi: *const normal.Formula) u8 {
    return switch (phi.*) {
        .atom => 1,
        .not => 2,
        .and_ => 3,
        .or_ => 4,
        .implies => 5,
        .box => 6,
        .dia => 7,
    };
}

fn forcesTrace(
    n: u32,
    rel: u32,
    val: u32,
    w: u32,
    phi: *const normal.Formula,
    steps: *std.ArrayList(Step),
    allocator: std.mem.Allocator,
) !bool {
    const r = switch (phi.*) {
        .atom => |a| (val & (@as(u32, 1) << @intCast(a * n + w))) != 0,
        .not => |x| !(try forcesTrace(n, rel, val, w, x, steps, allocator)),
        .and_ => |x| (try forcesTrace(n, rel, val, w, x.l, steps, allocator)) and
            (try forcesTrace(n, rel, val, w, x.r, steps, allocator)),
        .or_ => |x| (try forcesTrace(n, rel, val, w, x.l, steps, allocator)) or
            (try forcesTrace(n, rel, val, w, x.r, steps, allocator)),
        .implies => |x| !(try forcesTrace(n, rel, val, w, x.l, steps, allocator)) or
            (try forcesTrace(n, rel, val, w, x.r, steps, allocator)),
        .box => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and !(try forcesTrace(n, rel, val, v, x, steps, allocator))) break :blk false;
            }
            break :blk true;
        },
        .dia => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and (try forcesTrace(n, rel, val, v, x, steps, allocator))) break :blk true;
            }
            break :blk false;
        },
    };
    try steps.append(allocator, .{ .world = w, .tag = tagOf(phi), .result = r });
    return r;
}

pub fn traceForce(
    allocator: std.mem.Allocator,
    n: u32,
    rel: u32,
    val: u32,
    w: u32,
    phi: *const normal.Formula,
) !struct { result: bool, trace: Trace } {
    var steps: std.ArrayList(Step) = .empty;
    errdefer steps.deinit(allocator);
    const result = try forcesTrace(n, rel, val, w, phi, &steps, allocator);
    return .{ .result = result, .trace = .{ .steps = try steps.toOwnedSlice(allocator), .allocator = allocator } };
}

test "trace records steps for atom" {
    var arena = normal.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    // 1 world, p true
    var tr = try traceForce(std.testing.allocator, 1, 0b1, 0b1, 0, p);
    defer tr.trace.deinit();
    try std.testing.expect(tr.result);
    try std.testing.expect(tr.trace.steps.len >= 1);
    try std.testing.expect(tr.trace.steps[tr.trace.steps.len - 1].result == true);
}
