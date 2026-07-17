//! Giants interop — stand on industrial solvers / provers when installed.
//!
//! Discovery only + version probe. Full API bridges grow over time.
//! Never claim parity without scoreboard evidence.

const std = @import("std");

pub const Giant = enum {
    cadical,
    kissat,
    z3,
    abc,
    vampire,
    cvc5,
    drat_trim,
    lean,
    coq,
};

pub const Found = struct {
    giant: Giant,
    path: []const u8,
};

fn pathExists(path: []const u8) bool {
    if (path.len == 0 or path.len >= 400) return false;
    var buf: [512]u8 = undefined;
    @memcpy(buf[0..path.len], path);
    buf[path.len] = 0;
    const fd = std.os.linux.open(@ptrCast(&buf), .{ .ACCMODE = .RDONLY }, 0);
    if (@as(isize, @bitCast(fd)) < 0) return false;
    _ = std.os.linux.close(@intCast(fd));
    return true;
}

const Candidate = struct {
    giant: Giant,
    paths: []const []const u8,
};

const table = [_]Candidate{
    .{ .giant = .cadical, .paths = &.{
        "third_party/cadical/build/cadical",
        "third_party/cadical/cadical",
        "/usr/bin/cadical",
        "cadical",
    } },
    .{ .giant = .kissat, .paths = &.{
        "third_party/kissat/build/kissat",
        "/usr/bin/kissat",
        "kissat",
    } },
    .{ .giant = .z3, .paths = &.{
        "/usr/bin/z3",
        "z3",
        "third_party/z3/build/z3",
    } },
    .{ .giant = .abc, .paths = &.{
        "third_party/abc/abc",
        "/usr/bin/abc",
        "abc",
    } },
    .{ .giant = .vampire, .paths = &.{
        "/usr/bin/vampire",
        "vampire",
        "third_party/vampire/vampire",
    } },
    .{ .giant = .cvc5, .paths = &.{
        "/usr/bin/cvc5",
        "cvc5",
    } },
    .{ .giant = .drat_trim, .paths = &.{
        "third_party/drat-trim/drat-trim",
        "/usr/bin/drat-trim",
        "drat-trim",
    } },
    .{ .giant = .lean, .paths = &.{
        "/usr/bin/lean",
        "lean",
    } },
    .{ .giant = .coq, .paths = &.{
        "/usr/bin/coqc",
        "coqc",
    } },
};

/// Caller frees each Found.path and the slice.
pub fn discover(allocator: std.mem.Allocator) ![]Found {
    var out: std.ArrayList(Found) = .empty;
    errdefer {
        for (out.items) |f| allocator.free(f.path);
        out.deinit(allocator);
    }
    for (table) |c| {
        for (c.paths) |p| {
            if (pathExists(p)) {
                try out.append(allocator, .{
                    .giant = c.giant,
                    .path = try allocator.dupe(u8, p),
                });
                break;
            }
        }
    }
    return try out.toOwnedSlice(allocator);
}

pub fn printDiscover(allocator: std.mem.Allocator) !void {
    const found = try discover(allocator);
    defer {
        for (found) |f| allocator.free(f.path);
        allocator.free(found);
    }
    std.debug.print("=== GIANTS (installed) ===\n", .{});
    if (found.len == 0) {
        std.debug.print("(none found — install cadical/kissat/z3/abc/vampire/lean to stand on them)\n", .{});
        return;
    }
    for (found) |f| {
        std.debug.print("{s:12}  {s}\n", .{ @tagName(f.giant), f.path });
    }
    std.debug.print("count={d}\n", .{found.len});
}

test "discover does not crash" {
    const f = try discover(std.testing.allocator);
    for (f) |x| std.testing.allocator.free(x.path);
    std.testing.allocator.free(f);
}
