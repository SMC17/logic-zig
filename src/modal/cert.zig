//! Modal certificates — evidence objects for normal modal decisions.
//!
//! A **validity certificate** records that a formula was forced at every world
//! of every admitted frame/valuation in the finite bound.
//! A **countermodel certificate** records an explicit (n, relation, valuation,
//! world) witness where forcing fails, plus the system frame class.
//!
//! Checkers re-verify without trusting the producer Boolean.

const std = @import("std");
const normal = @import("normal.zig");

pub const ValidityCert = struct {
    system: normal.System,
    n_atoms: u32,
    max_n: u32,
    /// Hash fingerprint of formula structure for replay identity.
    formula_fingerprint: u64,
};

pub const CountermodelCert = struct {
    system: normal.System,
    n: u32,
    /// Bit-packed accessibility (n×n bits).
    relation: u32,
    /// Bit-packed valuation (n_atoms×n bits).
    valuation: u32,
    n_atoms: u32,
    /// World where forcing fails.
    world: u32,
    formula_fingerprint: u64,
};

pub const Cert = union(enum) {
    valid: ValidityCert,
    countermodel: CountermodelCert,
    bound_exceeded,
};

fn fingerprint(phi: *const normal.Formula) u64 {
    var h: u64 = 0xcbf29ce484222325;
    const prime: u64 = 0x100000001b3;
    const tag: u64 = switch (phi.*) {
        .atom => 1,
        .not => 2,
        .and_ => 3,
        .or_ => 4,
        .implies => 5,
        .box => 6,
        .dia => 7,
    };
    h ^= tag;
    h *%= prime;
    switch (phi.*) {
        .atom => |a| {
            h ^= a;
            h *%= prime;
        },
        .not => |x| h ^= fingerprint(x),
        .and_ => |x| {
            h ^= fingerprint(x.l);
            h *%= prime;
            h ^= fingerprint(x.r);
        },
        .or_ => |x| {
            h ^= fingerprint(x.l);
            h *%= prime;
            h ^= fingerprint(x.r);
        },
        .implies => |x| {
            h ^= fingerprint(x.l);
            h *%= prime;
            h ^= fingerprint(x.r);
        },
        .box => |x| h ^= fingerprint(x),
        .dia => |x| h ^= fingerprint(x),
    }
    h *%= prime;
    return h;
}

fn forces(n: u32, rel: u32, val: u32, w: u32, phi: *const normal.Formula, n_atoms: u32) bool {
    return switch (phi.*) {
        .atom => |a| (val & (@as(u32, 1) << @intCast(a * n + w))) != 0,
        .not => |x| !forces(n, rel, val, w, x, n_atoms),
        .and_ => |x| forces(n, rel, val, w, x.l, n_atoms) and forces(n, rel, val, w, x.r, n_atoms),
        .or_ => |x| forces(n, rel, val, w, x.l, n_atoms) or forces(n, rel, val, w, x.r, n_atoms),
        .implies => |x| !forces(n, rel, val, w, x.l, n_atoms) or forces(n, rel, val, w, x.r, n_atoms),
        .box => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and !forces(n, rel, val, v, x, n_atoms)) break :blk false;
            }
            break :blk true;
        },
        .dia => |x| blk: {
            var v: u32 = 0;
            while (v < n) : (v += 1) {
                const edge = (rel & (@as(u32, 1) << @intCast(w * n + v))) != 0;
                if (edge and forces(n, rel, val, v, x, n_atoms)) break :blk true;
            }
            break :blk false;
        },
    };
}

fn reflexive(n: u32, rel: u32) bool {
    var w: u32 = 0;
    while (w < n) : (w += 1) {
        if ((rel & (@as(u32, 1) << @intCast(w * n + w))) == 0) return false;
    }
    return true;
}
fn symmetric(n: u32, rel: u32) bool {
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        var j: u32 = 0;
        while (j < n) : (j += 1) {
            const ij = (rel & (@as(u32, 1) << @intCast(i * n + j))) != 0;
            const ji = (rel & (@as(u32, 1) << @intCast(j * n + i))) != 0;
            if (ij != ji) return false;
        }
    }
    return true;
}
fn transitive(n: u32, rel: u32) bool {
    var i: u32 = 0;
    while (i < n) : (i += 1) {
        var j: u32 = 0;
        while (j < n) : (j += 1) {
            var k: u32 = 0;
            while (k < n) : (k += 1) {
                const ij = (rel & (@as(u32, 1) << @intCast(i * n + j))) != 0;
                const jk = (rel & (@as(u32, 1) << @intCast(j * n + k))) != 0;
                const ik = (rel & (@as(u32, 1) << @intCast(i * n + k))) != 0;
                if (ij and jk and !ik) return false;
            }
        }
    }
    return true;
}
fn okFrame(sys: normal.System, n: u32, rel: u32) bool {
    return switch (sys) {
        .k => true,
        .t => reflexive(n, rel),
        .s4 => reflexive(n, rel) and transitive(n, rel),
        .s5 => reflexive(n, rel) and symmetric(n, rel) and transitive(n, rel),
    };
}

/// Produce a certificate for phi under system within the finite bound.
pub fn certify(sys: normal.System, phi: *const normal.Formula, n_atoms: u32, max_n: u32) Cert {
    if (max_n > 4 or n_atoms > 3) return .bound_exceeded;
    const fp = fingerprint(phi);
    var n: u32 = 1;
    while (n <= max_n) : (n += 1) {
        const rel_bits = n * n;
        const rel_full: u32 = if (rel_bits >= 32) 0xFFFF_FFFF else (@as(u32, 1) << @intCast(rel_bits)) - 1;
        var rel: u32 = 0;
        while (true) {
            if (okFrame(sys, n, rel)) {
                const val_bits = n_atoms * n;
                const val_full: u32 = if (val_bits >= 32) 0xFFFF_FFFF else (@as(u32, 1) << @intCast(val_bits)) - 1;
                var val: u32 = 0;
                while (true) {
                    var w: u32 = 0;
                    while (w < n) : (w += 1) {
                        if (!forces(n, rel, val, w, phi, n_atoms)) {
                            return .{ .countermodel = .{
                                .system = sys,
                                .n = n,
                                .relation = rel,
                                .valuation = val,
                                .n_atoms = n_atoms,
                                .world = w,
                                .formula_fingerprint = fp,
                            } };
                        }
                    }
                    if (val == val_full) break;
                    val += 1;
                }
            }
            if (rel == rel_full) break;
            rel += 1;
        }
    }
    return .{ .valid = .{
        .system = sys,
        .n_atoms = n_atoms,
        .max_n = max_n,
        .formula_fingerprint = fp,
    } };
}

/// Independent check of a countermodel certificate against phi.
pub fn checkCountermodel(cert: CountermodelCert, phi: *const normal.Formula) bool {
    if (fingerprint(phi) != cert.formula_fingerprint) return false;
    if (!okFrame(cert.system, cert.n, cert.relation)) return false;
    if (cert.world >= cert.n) return false;
    // Must actually fail forcing
    return !forces(cert.n, cert.relation, cert.valuation, cert.world, phi, cert.n_atoms);
}

/// Re-run decision and compare to validity cert fingerprint + bound.
pub fn checkValidity(cert: ValidityCert, phi: *const normal.Formula) bool {
    if (fingerprint(phi) != cert.formula_fingerprint) return false;
    const c = certify(cert.system, phi, cert.n_atoms, cert.max_n);
    return c == .valid;
}

test "countermodel cert for box-p-implies-p on K" {
    var arena = normal.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const bp = try arena.f(.{ .box = p });
    const imp = try arena.f(.{ .implies = .{ .l = bp, .r = p } });
    const c = certify(.k, imp, 1, 2);
    try std.testing.expect(c == .countermodel);
    try std.testing.expect(checkCountermodel(c.countermodel, imp));
}

test "validity cert for box-p-implies-p on T" {
    var arena = normal.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const bp = try arena.f(.{ .box = p });
    const imp = try arena.f(.{ .implies = .{ .l = bp, .r = p } });
    const c = certify(.t, imp, 1, 2);
    try std.testing.expect(c == .valid);
    try std.testing.expect(checkValidity(c.valid, imp));
}

test "mutated cert fails check" {
    var arena = normal.Arena.init(std.testing.allocator);
    defer arena.deinit();
    const p = try arena.f(.{ .atom = 0 });
    const bp = try arena.f(.{ .box = p });
    const imp = try arena.f(.{ .implies = .{ .l = bp, .r = p } });
    var c = certify(.k, imp, 1, 2);
    try std.testing.expect(c == .countermodel);
    c.countermodel.formula_fingerprint ^= 0xff;
    try std.testing.expect(!checkCountermodel(c.countermodel, imp));
}
