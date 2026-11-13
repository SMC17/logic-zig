//! Aristotelian categorical syllogistic — a complete decision procedure.
//!
//! Statements over terms S (minor), M (middle), P (major):
//!   A: all X are Y     E: no X is Y     I: some X is Y     O: some X is not Y
//!
//! A syllogism is mood (major, minor, conclusion statement types) × figure
//! (arrangement of M in the premises); 4×4×4×4 = 256 forms. A model is
//! determined up to satisfaction by which of the 8 Venn regions (S,M,P
//! membership patterns) are nonempty — so enumerating all 2^8 region
//! patterns is a **complete** semantics, not an approximation.
//!
//! Boolean (modern) semantics validates exactly 15 forms; adding existential
//! import (all three terms nonempty) validates the traditional 24.

const std = @import("std");

pub const StatementType = enum(u2) { a, e, i, o };

pub const Figure = enum(u2) {
    /// M–P, S–M
    first,
    /// P–M, S–M
    second,
    /// M–P, M–S
    third,
    /// P–M, M–S
    fourth,
};

/// Region index bit layout: bit0 = in S, bit1 = in M, bit2 = in P.
/// A "model" is the set of nonempty regions (u8 bitmask over 8 regions).
fn statementHolds(t: StatementType, x_bit: u3, y_bit: u3, regions: u8) bool {
    var some_xy = false;
    var some_x_not_y = false;
    for (0..8) |r| {
        if ((regions >> @intCast(r)) & 1 == 0) continue;
        const in_x = (r >> x_bit) & 1 == 1;
        const in_y = (r >> y_bit) & 1 == 1;
        if (in_x and in_y) some_xy = true;
        if (in_x and !in_y) some_x_not_y = true;
    }
    return switch (t) {
        .a => !some_x_not_y,
        .e => !some_xy,
        .i => some_xy,
        .o => some_x_not_y,
    };
}

const s_bit: u3 = 0;
const m_bit: u3 = 1;
const p_bit: u3 = 2;

pub const Syllogism = struct {
    major: StatementType, // premise containing P
    minor: StatementType, // premise containing S
    conclusion: StatementType, // S–P
    figure: Figure,
};

pub const Certificate = struct {
    valid: bool,
    /// Exact set of premise-satisfying region models for a valid result.
    eligible_models: [4]u64 = .{ 0, 0, 0, 0 },
    /// Replayable Venn-region countermodel for an invalid result.
    countermodel: ?u8 = null,
};

fn setModel(bits: *[4]u64, model: u8) void {
    bits[model / 64] |= @as(u64, 1) << @intCast(model % 64);
}

fn hasModel(bits: *const [4]u64, model: u8) bool {
    return (bits[model / 64] >> @intCast(model % 64)) & 1 == 1;
}

fn premisesHold(sy: Syllogism, regions: u8) bool {
    const major_ok = switch (sy.figure) {
        .first, .third => statementHolds(sy.major, m_bit, p_bit, regions), // M–P
        .second, .fourth => statementHolds(sy.major, p_bit, m_bit, regions), // P–M
    };
    if (!major_ok) return false;
    return switch (sy.figure) {
        .first, .second => statementHolds(sy.minor, s_bit, m_bit, regions), // S–M
        .third, .fourth => statementHolds(sy.minor, m_bit, s_bit, regions), // M–S
    };
}

fn termsNonempty(regions: u8) bool {
    var s = false;
    var m = false;
    var p = false;
    for (0..8) |r| {
        if ((regions >> @intCast(r)) & 1 == 0) continue;
        if ((r >> s_bit) & 1 == 1) s = true;
        if ((r >> m_bit) & 1 == 1) m = true;
        if ((r >> p_bit) & 1 == 1) p = true;
    }
    return s and m and p;
}

/// Complete decision with replayable exhaustive/countermodel evidence.
pub fn decide(sy: Syllogism, existential_import: bool) Certificate {
    var certificate: Certificate = .{ .valid = true };
    var regions: u32 = 0;
    while (regions < 256) : (regions += 1) {
        const rr: u8 = @intCast(regions);
        if (existential_import and !termsNonempty(rr)) continue;
        if (!premisesHold(sy, rr)) continue;
        setModel(&certificate.eligible_models, rr);
        if (!statementHolds(sy.conclusion, s_bit, p_bit, rr)) {
            certificate.valid = false;
            certificate.countermodel = rr;
            certificate.eligible_models = .{ 0, 0, 0, 0 };
            return certificate;
        }
    }
    return certificate;
}

/// Is the syllogism valid? Complete check over all 256 region patterns.
pub fn valid(sy: Syllogism, existential_import: bool) bool {
    return decide(sy, existential_import).valid;
}

/// Small evidence checker independent of the decision traversal state.
pub fn verifyCertificate(sy: Syllogism, existential_import: bool, certificate: Certificate) bool {
    if (!certificate.valid) {
        const model = certificate.countermodel orelse return false;
        if (existential_import and !termsNonempty(model)) return false;
        return premisesHold(sy, model) and !statementHolds(sy.conclusion, s_bit, p_bit, model);
    }
    if (certificate.countermodel != null) return false;
    var regions: u32 = 0;
    while (regions < 256) : (regions += 1) {
        const model: u8 = @intCast(regions);
        const eligible = (!existential_import or termsNonempty(model)) and premisesHold(sy, model);
        if (hasModel(&certificate.eligible_models, model) != eligible) return false;
        if (eligible and !statementHolds(sy.conclusion, s_bit, p_bit, model)) return false;
    }
    return true;
}

/// Count valid forms among all 256.
pub fn countValid(existential_import: bool) u32 {
    var count: u32 = 0;
    for (0..4) |maj| {
        for (0..4) |min| {
            for (0..4) |con| {
                for (0..4) |fig| {
                    const sy = Syllogism{
                        .major = @enumFromInt(maj),
                        .minor = @enumFromInt(min),
                        .conclusion = @enumFromInt(con),
                        .figure = @enumFromInt(fig),
                    };
                    if (valid(sy, existential_import)) count += 1;
                }
            }
        }
    }
    return count;
}

// ── Tests ────────────────────────────────────────────────────────────

const testing = std.testing;

test "syllogistic: exactly 15 Boolean-valid and 24 with existential import" {
    try testing.expectEqual(@as(u32, 15), countValid(false));
    try testing.expectEqual(@as(u32, 24), countValid(true));
}

test "syllogistic: named canon forms" {
    // Barbara AAA-1: valid unconditionally.
    const barbara = Syllogism{ .major = .a, .minor = .a, .conclusion = .a, .figure = .first };
    try testing.expect(valid(barbara, false));
    try testing.expect(valid(barbara, true));

    // Celarent EAE-1: valid unconditionally.
    const celarent = Syllogism{ .major = .e, .minor = .a, .conclusion = .e, .figure = .first };
    try testing.expect(valid(celarent, false));

    // Darii AII-1 and Ferio EIO-1: valid unconditionally.
    try testing.expect(valid(.{ .major = .a, .minor = .i, .conclusion = .i, .figure = .first }, false));
    try testing.expect(valid(.{ .major = .e, .minor = .i, .conclusion = .o, .figure = .first }, false));

    // Darapti AAI-3: only valid with existential import.
    const darapti = Syllogism{ .major = .a, .minor = .a, .conclusion = .i, .figure = .third };
    try testing.expect(!valid(darapti, false));
    try testing.expect(valid(darapti, true));

    // Barbari AAI-1: subaltern — import only.
    const barbari = Syllogism{ .major = .a, .minor = .a, .conclusion = .i, .figure = .first };
    try testing.expect(!valid(barbari, false));
    try testing.expect(valid(barbari, true));

    // AAA-2: the classic undistributed-middle fallacy — invalid both ways.
    const aaa2 = Syllogism{ .major = .a, .minor = .a, .conclusion = .a, .figure = .second };
    try testing.expect(!valid(aaa2, false));
    try testing.expect(!valid(aaa2, true));

    // Camestres AEE-2, Baroco AOO-2: valid unconditionally.
    try testing.expect(valid(.{ .major = .a, .minor = .e, .conclusion = .e, .figure = .second }, false));
    try testing.expect(valid(.{ .major = .a, .minor = .o, .conclusion = .o, .figure = .second }, false));

    // Bocardo OAO-3: valid unconditionally.
    try testing.expect(valid(.{ .major = .o, .minor = .a, .conclusion = .o, .figure = .third }, false));
}

test "syllogistic: import-valid set strictly contains Boolean-valid set" {
    for (0..4) |maj| {
        for (0..4) |min| {
            for (0..4) |con| {
                for (0..4) |fig| {
                    const sy = Syllogism{
                        .major = @enumFromInt(maj),
                        .minor = @enumFromInt(min),
                        .conclusion = @enumFromInt(con),
                        .figure = @enumFromInt(fig),
                    };
                    if (valid(sy, false)) try testing.expect(valid(sy, true));
                }
            }
        }
    }
}

test "syllogistic: every form returns replayable evidence" {
    for (0..4) |maj| {
        for (0..4) |min| {
            for (0..4) |con| {
                for (0..4) |fig| {
                    const sy = Syllogism{
                        .major = @enumFromInt(maj),
                        .minor = @enumFromInt(min),
                        .conclusion = @enumFromInt(con),
                        .figure = @enumFromInt(fig),
                    };
                    for ([_]bool{ false, true }) |with_import| {
                        const certificate = decide(sy, with_import);
                        try testing.expect(verifyCertificate(sy, with_import, certificate));
                        if (!certificate.valid) try testing.expect(certificate.countermodel != null);
                    }
                }
            }
        }
    }
}

test "syllogistic: certificate mutation is rejected" {
    const barbara = Syllogism{ .major = .a, .minor = .a, .conclusion = .a, .figure = .first };
    var certificate = decide(barbara, false);
    certificate.eligible_models[0] ^= 1;
    try testing.expect(!verifyCertificate(barbara, false, certificate));

    const aaa2 = Syllogism{ .major = .a, .minor = .a, .conclusion = .a, .figure = .second };
    var invalid = decide(aaa2, false);
    invalid.countermodel = 0;
    try testing.expect(!verifyCertificate(aaa2, false, invalid));
}
