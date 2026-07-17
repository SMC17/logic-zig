//! IC3 entry point — full engine lives in `pdr.zig` (MIC + push + fixed-point).
//! This module re-exports for stable `logic.ic3` API compatibility.

const pdr = @import("pdr.zig");

pub const Ic3Status = pdr.PdrStatus;
pub const Ic3Result = pdr.PdrResult;
pub const check = pdr.check;

test "ic3 reexport stuck0" {
    const netlist_mod = @import("netlist.zig");
    const std = @import("std");
    var nl = netlist_mod.Netlist.init(std.testing.allocator);
    defer nl.deinit();
    const q = try nl.allocNetNamed("q");
    const d = try nl.allocNetNamed("d");
    try nl.addConst(d, false);
    try nl.addLatch(d, q, false);
    const r = try check(std.testing.allocator, &nl, q, 12);
    defer if (r.cex_latches) |c| std.testing.allocator.free(c);
    try std.testing.expect(r.status != .violated);
}
