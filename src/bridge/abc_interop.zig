//! Optional ABC interop — invoke `abc` if present for differential / baseline.
//!
//! Does not vendor ABC. Discovery: `LOGIC_ZIG_ABC` via /proc environ,
//! `third_party/abc/abc`, `/usr/bin/abc`.

const std = @import("std");

pub const AbcStatus = enum {
    unavailable,
    ok,
    failed,
};

pub const AbcResult = struct {
    status: AbcStatus,
    output: ?[]u8 = null,
    path: ?[]u8 = null,
};

fn pathExists(path: []const u8) bool {
    var buf: [512]u8 = undefined;
    if (path.len >= buf.len) return false;
    @memcpy(buf[0..path.len], path);
    buf[path.len] = 0;
    const fd = std.os.linux.open(@ptrCast(&buf), .{ .ACCMODE = .RDONLY }, 0);
    if (@as(isize, @bitCast(fd)) < 0) return false;
    _ = std.os.linux.close(@intCast(fd));
    return true;
}

fn readEnvAbc(allocator: std.mem.Allocator) ?[]const u8 {
    const fd = std.os.linux.open("/proc/self/environ", .{ .ACCMODE = .RDONLY }, 0);
    if (@as(isize, @bitCast(fd)) < 0) return null;
    defer _ = std.os.linux.close(@intCast(fd));
    var buf: [8192]u8 = undefined;
    const n = std.os.linux.read(@intCast(fd), &buf, buf.len);
    if (@as(isize, @bitCast(n)) <= 0) return null;
    const data = buf[0..@intCast(n)];
    const key = "LOGIC_ZIG_ABC=";
    var start: usize = 0;
    while (start < data.len) {
        const end = std.mem.indexOfScalarPos(u8, data, start, 0) orelse data.len;
        const entry = data[start..end];
        if (std.mem.startsWith(u8, entry, key)) {
            const val = entry[key.len..];
            if (val.len > 0 and pathExists(val)) return allocator.dupe(u8, val) catch null;
        }
        start = end + 1;
    }
    return null;
}

pub fn findAbc(allocator: std.mem.Allocator) !?[]u8 {
    if (readEnvAbc(allocator)) |p| return @constCast(p);
    const candidates = [_][]const u8{
        "third_party/abc/abc",
        "/usr/bin/abc",
        "/usr/local/bin/abc",
    };
    for (candidates) |c| {
        if (pathExists(c)) return try allocator.dupe(u8, c);
    }
    return null;
}

pub fn doctor(allocator: std.mem.Allocator) ![]const u8 {
    if (try findAbc(allocator)) |p| {
        defer allocator.free(p);
        return try std.fmt.allocPrint(allocator, "abc: {s}", .{p});
    }
    return try allocator.dupe(u8, "abc: UNAVAILABLE (set LOGIC_ZIG_ABC)");
}

test "abc find does not crash" {
    const p = try findAbc(std.testing.allocator);
    if (p) |x| std.testing.allocator.free(x);
}
