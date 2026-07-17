//! Minimal IPASIR-style consumer (Zig API) — external gravity example.
//! Build: linked via `zig build` examples step or `zig test` this file with logic module.
//!
//!   const logic = @import("logic");
//!   var s = logic.IpasirSolver.init(gpa);
//!   try s.add(1); try s.add(2); try s.add(0);
//!   _ = try s.solve();

const std = @import("std");
const logic = @import("logic");

pub fn main(init: std.process.Init) !void {
    const gpa = init.gpa;
    var s = logic.IpasirSolver.init(gpa);
    defer s.deinit();

    // (x ∨ y) ∧ (¬x ∨ y)  ⇒  y
    try s.add(1);
    try s.add(2);
    try s.add(0);
    try s.add(-1);
    try s.add(2);
    try s.add(0);

    const r = try s.solve();
    std.debug.print("solve1={s} y={d}\n", .{ @tagName(r), s.val(2) });

    // Force ¬y → unsat
    try s.assume(-2);
    const r2 = try s.solve();
    std.debug.print("solve2={s} failed(-2)={d}\n", .{ @tagName(r2), s.failed(-2) });

    // Multishot: without assume still sat
    const r3 = try s.solve();
    std.debug.print("solve3={s}\n", .{@tagName(r3)});
    std.debug.print("IPASIR_CONSUMER_OK signature={s}\n", .{logic.ipasir.IpasirSolver.signature()});
}
