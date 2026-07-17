//! Optional ABC interop — invoke `abc` if present for differential / baseline.
//!
//! Does not vendor ABC. Discovery: `LOGIC_ZIG_ABC` via /proc environ,
//! `third_party/abc/abc`, `/usr/bin/abc`.
//!
//! Industrial MC path: when ABC is present, run a safety-style script on an
//! AIGER file and parse a coarse status for Δ vs internal engines.

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

    pub fn deinit(self: *AbcResult, allocator: std.mem.Allocator) void {
        if (self.output) |o| allocator.free(o);
        if (self.path) |p| allocator.free(p);
        self.* = undefined;
    }
};

/// Coarse safety result from ABC (or unavailable).
pub const SafetyStatus = enum { proven, violated, unknown, unavailable, error_ };

pub const SafetyResult = struct {
    status: SafetyStatus,
    abc_path: ?[]const u8 = null,
    log: ?[]u8 = null,

    pub fn deinit(self: *SafetyResult, allocator: std.mem.Allocator) void {
        if (self.abc_path) |p| allocator.free(p);
        if (self.log) |l| allocator.free(l);
        self.* = undefined;
    }
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

/// Run ABC on an AIGER path with a short PDR/BMC-style script.
/// Soft: if ABC missing or script fails → unavailable/unknown (not a hard error).
pub fn checkAigerSafety(
    allocator: std.mem.Allocator,
    io: std.Io,
    aiger_path: []const u8,
) !SafetyResult {
    const abc = try findAbc(allocator) orelse return .{ .status = .unavailable };
    // ABC interactive-ish: echo commands. Prefer -c if supported.
    // Common pattern: abc -c "read_aiger foo.aig; &get; &pdr; &cex -m"
    const cmd = try std.fmt.allocPrint(allocator, "read_aiger {s}; pdr; empty", .{aiger_path});
    defer allocator.free(cmd);

    const result = std.process.run(allocator, io, .{
        .argv = &.{ abc, "-c", cmd },
        .stdout_limit = .limited(2 * 1024 * 1024),
        .stderr_limit = .limited(512 * 1024),
    }) catch {
        return .{ .status = .error_, .abc_path = abc };
    };
    defer allocator.free(result.stderr);
    // Keep stdout as log
    const out = result.stdout;
    var status: SafetyStatus = .unknown;
    // Heuristic parse
    if (std.mem.indexOf(u8, out, "Property proved") != null or
        std.mem.indexOf(u8, out, "proved") != null or
        std.mem.indexOf(u8, out, "UNSAT") != null)
    {
        status = .proven;
    } else if (std.mem.indexOf(u8, out, "Counter-example") != null or
        std.mem.indexOf(u8, out, "Counterexample") != null or
        std.mem.indexOf(u8, out, "SATISFIABLE") != null or
        std.mem.indexOf(u8, out, "cex") != null)
    {
        status = .violated;
    }
    return .{ .status = status, .abc_path = abc, .log = out };
}

/// Compare internal MC status string to ABC when available.
pub fn deltaLabel(internal_proven: bool, internal_violated: bool, abc: SafetyStatus) []const u8 {
    return switch (abc) {
        .unavailable => "abc_skip",
        .error_ => "abc_error",
        .unknown => "abc_unknown",
        .proven => if (internal_proven) "agree_proven" else if (internal_violated) "MISMATCH" else "abc_only_proven",
        .violated => if (internal_violated) "agree_violated" else if (internal_proven) "MISMATCH" else "abc_only_violated",
    };
}

test "abc find does not crash" {
    const p = try findAbc(std.testing.allocator);
    if (p) |x| std.testing.allocator.free(x);
}

test "delta label" {
    try std.testing.expectEqualStrings("abc_skip", deltaLabel(true, false, .unavailable));
    try std.testing.expectEqualStrings("agree_proven", deltaLabel(true, false, .proven));
    try std.testing.expectEqualStrings("MISMATCH", deltaLabel(true, false, .violated));
}
