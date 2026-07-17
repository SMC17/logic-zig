//! IPASIR C ABI — link into shared library with libc.

const std = @import("std");
const ipasir = @import("ipasir.zig");

const CSolver = ipasir.IpasirSolver;

export fn ipasir_signature() callconv(.c) [*:0]const u8 {
    return CSolver.signature();
}

export fn ipasir_init() callconv(.c) ?*anyopaque {
    const allocator = std.heap.c_allocator;
    const s = allocator.create(CSolver) catch return null;
    s.* = CSolver.init(allocator);
    return s;
}

export fn ipasir_release(solver: ?*anyopaque) callconv(.c) void {
    if (solver == null) return;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    const allocator = s.allocator;
    s.deinit();
    allocator.destroy(s);
}

export fn ipasir_add(solver: ?*anyopaque, lit_or_zero: c_int) callconv(.c) void {
    if (solver == null) return;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    s.add(lit_or_zero) catch {};
}

export fn ipasir_assume(solver: ?*anyopaque, lit: c_int) callconv(.c) void {
    if (solver == null) return;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    s.assume(lit) catch {};
}

export fn ipasir_solve(solver: ?*anyopaque) callconv(.c) c_int {
    if (solver == null) return 0;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    const r = s.solve() catch return 0;
    return @intFromEnum(r);
}

export fn ipasir_val(solver: ?*anyopaque, lit: c_int) callconv(.c) c_int {
    if (solver == null) return 0;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    return s.val(lit);
}

export fn ipasir_failed(solver: ?*anyopaque, lit: c_int) callconv(.c) c_int {
    if (solver == null) return 0;
    const s: *CSolver = @ptrCast(@alignCast(solver));
    return s.failed(lit);
}

/// Partial IPASIR: termination callback not yet wired (no-op).
export fn ipasir_set_terminate(solver: ?*anyopaque, state: ?*anyopaque, cb: ?*const fn (?*anyopaque) callconv(.c) c_int) callconv(.c) void {
    _ = solver;
    _ = state;
    _ = cb;
}

/// Partial IPASIR: learned-clause callback not yet wired (no-op).
export fn ipasir_set_learn(solver: ?*anyopaque, state: ?*anyopaque, max_len: c_int, cb: ?*const fn (?*anyopaque, [*c]const c_int) callconv(.c) void) callconv(.c) void {
    _ = solver;
    _ = state;
    _ = max_len;
    _ = cb;
}
