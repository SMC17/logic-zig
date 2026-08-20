//! Automated sequent proof search — backward chaining on classical prop LK.
//!
//! Goal: decide Γ ⊢ Δ for propositional formulas built from atoms + ¬∧∨→.
//! Strategy: invert rules bottom-up (goal-directed), prefer invertible rules,
//! terminate on initial sequents or depth bound.
//!
//! Fragment: depth-bounded search with formula multiset contexts represented
//! as sorted atom/polarity bags for the propositional core. Full first-order
//! focusing is future work.

const std = @import("std");
const sequent = @import("sequent.zig");

pub const SearchOptions = struct {
    max_depth: u32 = 32,
};

pub const SearchResult = enum { proved, failed, depth_exceeded };

/// Atom-level sequent for the automated core: left and right are multisets of
/// signed atoms (positive = right-side atom or left-side negation, etc.).
/// For the spine we reduce formulas to NNF-ish signed literals via a simple
/// recursive inversion.

pub const Signed = struct {
    atom: []const u8,
    /// true = positive occurrence on the side it sits
    pos: bool,
};

fn signedEql(a: Signed, b: Signed) bool {
    return a.pos == b.pos and std.mem.eql(u8, a.atom, b.atom);
}

fn hasInitial(left: []const Signed, right: []const Signed) bool {
    for (left) |l| {
        for (right) |r| {
            if (signedEql(l, r)) return true;
        }
    }
    return false;
}

/// Prove a purely atomic sequent (all formulas already decomposed to signed atoms).
pub fn proveAtomic(left: []const Signed, right: []const Signed) bool {
    return hasInitial(left, right);
}

/// Recursive proof search over Formula sequents using sequent.zig types.
pub fn search(
    allocator: std.mem.Allocator,
    goal: sequent.Sequent,
    opts: SearchOptions,
) !SearchResult {
    return searchDepth(allocator, goal, opts.max_depth);
}

fn searchDepth(allocator: std.mem.Allocator, goal: sequent.Sequent, depth: u32) !SearchResult {
    _ = allocator;
    if (goal.isInitial()) return .proved;
    if (depth == 0) return .depth_exceeded;

    // Invert right-∧ : Γ ⊢ Δ, A∧B  ←  Γ ⊢ Δ,A  and  Γ ⊢ Δ,B
    for (goal.right.formulas, 0..) |phi, idx| {
        if (phi.* == .and_) {
            const a = phi.and_.l;
            const b = phi.and_.r;
            // Build Δ without this formula + A / + B
            var right_a: [16]*sequent.Formula = undefined;
            var right_b: [16]*sequent.Formula = undefined;
            var n: usize = 0;
            for (goal.right.formulas, 0..) |f, j| {
                if (j == idx) continue;
                if (n >= 15) break;
                right_a[n] = f;
                right_b[n] = f;
                n += 1;
            }
            right_a[n] = a;
            right_b[n] = b;
            const sa = sequent.Sequent{
                .left = goal.left,
                .right = .{ .formulas = right_a[0 .. n + 1] },
            };
            const sb = sequent.Sequent{
                .left = goal.left,
                .right = .{ .formulas = right_b[0 .. n + 1] },
            };
            const ra = try searchDepth(allocator, sa, depth - 1);
            if (ra != .proved) continue;
            const rb = try searchDepth(allocator, sb, depth - 1);
            if (rb == .proved) return .proved;
        }
        if (phi.* == .implies) {
            // Γ ⊢ Δ, A→B  ←  Γ,A ⊢ Δ,B
            const ant = phi.implies.l;
            const cons = phi.implies.r;
            var left_buf: [16]*sequent.Formula = undefined;
            var right_buf: [16]*sequent.Formula = undefined;
            var nl: usize = 0;
            for (goal.left.formulas) |f| {
                if (nl >= 15) break;
                left_buf[nl] = f;
                nl += 1;
            }
            left_buf[nl] = ant;
            nl += 1;
            var nr: usize = 0;
            for (goal.right.formulas, 0..) |f, j| {
                if (j == idx) continue;
                if (nr >= 15) break;
                right_buf[nr] = f;
                nr += 1;
            }
            right_buf[nr] = cons;
            nr += 1;
            const sub = sequent.Sequent{
                .left = .{ .formulas = left_buf[0..nl] },
                .right = .{ .formulas = right_buf[0..nr] },
            };
            const r = try searchDepth(allocator, sub, depth - 1);
            if (r == .proved) return .proved;
        }
    }

    // Invert left-∧ : Γ, A∧B ⊢ Δ  ←  Γ,A,B ⊢ Δ
    for (goal.left.formulas, 0..) |phi, idx| {
        if (phi.* == .and_) {
            const a = phi.and_.l;
            const b = phi.and_.r;
            var left_buf: [16]*sequent.Formula = undefined;
            var n: usize = 0;
            for (goal.left.formulas, 0..) |f, j| {
                if (j == idx) continue;
                if (n >= 14) break;
                left_buf[n] = f;
                n += 1;
            }
            left_buf[n] = a;
            left_buf[n + 1] = b;
            const sub = sequent.Sequent{
                .left = .{ .formulas = left_buf[0 .. n + 2] },
                .right = goal.right,
            };
            const r = try searchDepth(allocator, sub, depth - 1);
            if (r == .proved) return .proved;
        }
    }

    return .failed;
}

test "atomic initial proved" {
    var arena = sequent.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = "P" });
    const g = sequent.Sequent{
        .left = .{ .formulas = &[_]*sequent.Formula{p} },
        .right = .{ .formulas = &[_]*sequent.Formula{p} },
    };
    const r = try search(std.testing.allocator, g, .{});
    try std.testing.expect(r == .proved);
}

test "P implies P via search" {
    var arena = sequent.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = "P" });
    const imp = try arena.f(.{ .implies = .{ .l = p, .r = p } });
    const g = sequent.Sequent{
        .left = .{ .formulas = &[_]*sequent.Formula{} },
        .right = .{ .formulas = &[_]*sequent.Formula{imp} },
    };
    const r = try search(std.testing.allocator, g, .{ .max_depth = 8 });
    try std.testing.expect(r == .proved);
}

test "atomic mismatch fails" {
    var arena = sequent.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = "P" });
    const q = try arena.f(.{ .atom = "Q" });
    const g = sequent.Sequent{
        .left = .{ .formulas = &[_]*sequent.Formula{p} },
        .right = .{ .formulas = &[_]*sequent.Formula{q} },
    };
    const r = try search(std.testing.allocator, g, .{});
    try std.testing.expect(r == .failed);
}
