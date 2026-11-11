//! Host operations use Zig's platform-aware backend instead of Linux syscall
//! numbers. Keep the existing no-Io discovery APIs on the startup debug backend;
//! operations which already receive an Io continue to use their caller's backend.
const std = @import("std");
const builtin = @import("builtin");

pub fn pathExists(path: []const u8) bool {
    if (path.len == 0) return false;
    std.Io.Dir.cwd().access(std.Options.debug_io, path, .{ .read = true }) catch return false;
    return true;
}

pub fn executableExists(path: []const u8) bool {
    const stat = std.Io.Dir.cwd().statFile(std.Options.debug_io, path, .{}) catch return false;
    if (stat.kind != .file) return false;
    std.Io.Dir.cwd().access(std.Options.debug_io, path, .{ .execute = true }) catch return false;
    return true;
}

pub fn executableDir(allocator: std.mem.Allocator) ?[]u8 {
    const exe = std.process.executablePathAlloc(std.Options.debug_io, allocator) catch return null;
    defer allocator.free(exe);
    const dir = std.fs.path.dirname(exe) orelse return null;
    return allocator.dupe(u8, dir) catch null;
}

/// Discovery reads the process-start environment, not a truncated /proc file.
/// Test runners supply their own startup environment through std.testing.
pub fn envPath(allocator: std.mem.Allocator, key: []const u8) ?[]const u8 {
    const environ = if (builtin.is_test)
        std.testing.environ
    else if (std.Options.debug_threaded_io) |threaded|
        threaded.environ.process_environ
    else
        std.process.Environ.empty;
    const path = environ.getAlloc(allocator, key) catch return null;
    if (executableExists(path)) return path;
    allocator.free(path);
    return null;
}

pub fn monoNs() u64 {
    return @intCast(std.Io.Clock.awake.now(std.Options.debug_io).nanoseconds);
}

/// writeFile handles short writes and reports errors before callers invoke a tool
/// or announce that a proof/export was saved.
pub fn writeFile(io: std.Io, path: []const u8, body: []const u8) !void {
    try std.Io.Dir.cwd().writeFile(io, .{ .sub_path = path, .data = body });
}

test "host clock and executable discovery run on the native platform" {
    const before = monoNs();
    const dir = executableDir(std.testing.allocator) orelse return error.ExecutableNotFound;
    defer std.testing.allocator.free(dir);
    try std.testing.expect(std.fs.path.isAbsolute(dir));
    try std.testing.expect(monoNs() >= before);
    try std.testing.expect(!pathExists(""));
    try std.testing.expect(!pathExists(".zig-cache/no-such-host-file"));
}

test "host writes complete data, truncates old output, and propagates failure" {
    var tmp = std.testing.tmpDir(.{});
    defer tmp.cleanup();
    const path = try std.fmt.allocPrint(std.testing.allocator, ".zig-cache/tmp/{s}/output", .{tmp.sub_path});
    defer std.testing.allocator.free(path);
    const io = std.testing.io;
    const body = [_]u8{0xa5} ** (128 * 1024);
    try writeFile(io, path, &body);
    const read = try std.Io.Dir.cwd().readFileAlloc(io, path, std.testing.allocator, .limited(body.len + 1));
    defer std.testing.allocator.free(read);
    try std.testing.expectEqualSlices(u8, &body, read);
    try std.testing.expect(pathExists(path));
    try std.testing.expect(!executableExists(path));
    try std.testing.expect(!executableExists(".zig-cache"));
    try writeFile(io, path, "short");
    const stat = try std.Io.Dir.cwd().statFile(io, path, .{});
    try std.testing.expectEqual(@as(u64, 5), stat.size);
    try std.testing.expectError(error.FileNotFound, writeFile(io, ".zig-cache/no-such-host-parent/output", "x"));
}
