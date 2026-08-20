//! Reiter default logic — propositional fragment.
//!
//! A default is  α : β / γ  (prerequisite : justifications / consequent).
//! An extension is a fixed-point of the deductive closure under applicable defaults.
//!
//! Fragment: finite default theories over propositional atoms, exhaustive
//! generation of candidate extensions for small theories (≤12 defaults).
//! Uses classical consequence via the CDCL stack when available; for the
//! spine we encode consequence as explicit Horn/unit closure over atoms.
//!
//! Not a full prioritized / normal-default industrial engine.

const std = @import("std");

pub const Atom = u32;

/// Literal: positive atom or negation.
pub const Literal = struct {
    atom: Atom,
    neg: bool = false,

    pub fn pos(a: Atom) Literal {
        return .{ .atom = a, .neg = false };
    }
    pub fn n(a: Atom) Literal {
        return .{ .atom = a, .neg = true };
    }
};

pub const Default = struct {
    /// Prerequisite (conjunction of literals). Empty = true.
    prereq: []const Literal,
    /// Justifications — each must be consistent with the extension.
    justifications: []const Literal,
    /// Consequent (conjunction added when applied).
    consequent: []const Literal,
};

pub const Theory = struct {
    /// Background facts (units).
    facts: []const Literal,
    defaults: []const Default,
};

/// Bitset of signed literals: atom i positive = bit 2i, negative = bit 2i+1.
/// Caps at 16 atoms for the fragment.
pub const State = struct {
    bits: u32 = 0,

    pub fn has(self: State, lit: Literal) bool {
        const bit: u5 = @intCast(lit.atom * 2 + @as(u32, @intFromBool(lit.neg)));
        return (self.bits & (@as(u32, 1) << bit)) != 0;
    }

    pub fn add(self: *State, lit: Literal) void {
        const bit: u5 = @intCast(lit.atom * 2 + @as(u32, @intFromBool(lit.neg)));
        self.bits |= @as(u32, 1) << bit;
    }

    pub fn consistent(self: State) bool {
        var a: u32 = 0;
        while (a < 16) : (a += 1) {
            const pos_bit: u5 = @intCast(a * 2);
            const neg_bit: u5 = @intCast(a * 2 + 1);
            const has_pos = (self.bits & (@as(u32, 1) << pos_bit)) != 0;
            const has_neg = (self.bits & (@as(u32, 1) << neg_bit)) != 0;
            if (has_pos and has_neg) return false;
        }
        return true;
    }

    pub fn entailsAll(self: State, lits: []const Literal) bool {
        for (lits) |l| {
            if (!self.has(l)) return false;
        }
        return true;
    }

    pub fn consistentWith(self: State, lit: Literal) bool {
        var s = self;
        s.add(lit);
        return s.consistent();
    }
};

fn applyDefaults(theory: *const Theory, seed: State, used_mask: u32) State {
    var state = seed;
    for (theory.facts) |f| state.add(f);

    // Iterate to fixed point under selected defaults (mask).
    var changed = true;
    while (changed) {
        changed = false;
        for (theory.defaults, 0..) |d, i| {
            if ((used_mask & (@as(u32, 1) << @intCast(i))) == 0) continue;
            if (!state.entailsAll(d.prereq)) continue;
            var just_ok = true;
            for (d.justifications) |j| {
                if (!state.consistentWith(j)) {
                    just_ok = false;
                    break;
                }
            }
            if (!just_ok) continue;
            for (d.consequent) |c| {
                if (!state.has(c)) {
                    state.add(c);
                    changed = true;
                }
            }
        }
    }
    return state;
}

/// A set of defaults is generating if applying exactly those yields a state
/// where precisely those defaults are applicable (Reiter extension condition).
pub fn isExtension(theory: *const Theory, mask: u32) bool {
    const n = theory.defaults.len;
    if (n > 12) return false;

    var seed: State = .{};
    for (theory.facts) |f| seed.add(f);
    if (!seed.consistent()) return false;

    const state = applyDefaults(theory, seed, mask);
    if (!state.consistent()) return false;

    // Check applicability matches mask.
    for (theory.defaults, 0..) |d, i| {
        const selected = (mask & (@as(u32, 1) << @intCast(i))) != 0;
        const prereq_ok = state.entailsAll(d.prereq);
        var just_ok = true;
        for (d.justifications) |j| {
            if (!state.consistentWith(j)) {
                just_ok = false;
                break;
            }
        }
        const applicable = prereq_ok and just_ok;
        if (selected != applicable) return false;
    }
    return true;
}

pub const ExtensionResult = struct {
    masks: []u32,
    allocator: std.mem.Allocator,

    pub fn deinit(self: *ExtensionResult) void {
        self.allocator.free(self.masks);
        self.* = undefined;
    }
};

/// Enumerate all Reiter extensions (masks over defaults).
pub fn extensions(allocator: std.mem.Allocator, theory: *const Theory) !ExtensionResult {
    const n = theory.defaults.len;
    if (n > 12) return error.TooManyDefaults;
    const full: u32 = if (n == 0) 0 else (@as(u32, 1) << @intCast(n)) - 1;

    var list: std.ArrayList(u32) = .empty;
    errdefer list.deinit(allocator);

    var mask: u32 = 0;
    while (mask <= full) : (mask += 1) {
        if (isExtension(theory, mask)) {
            try list.append(allocator, mask);
        }
    }
    return .{ .masks = try list.toOwnedSlice(allocator), .allocator = allocator };
}

test "empty theory one empty extension" {
    const th = Theory{ .facts = &[_]Literal{}, .defaults = &[_]Default{} };
    var res = try extensions(std.testing.allocator, &th);
    defer res.deinit();
    try std.testing.expect(res.masks.len == 1);
    try std.testing.expect(res.masks[0] == 0);
}

test "normal default applies" {
    // Fact: none. Default: : a / a  (normal default concluding a)
    const a = Literal.pos(0);
    const d = Default{
        .prereq = &[_]Literal{},
        .justifications = &[_]Literal{a},
        .consequent = &[_]Literal{a},
    };
    const th = Theory{ .facts = &[_]Literal{}, .defaults = &[_]Default{d} };
    try std.testing.expect(isExtension(&th, 1)); // apply default
    try std.testing.expect(!isExtension(&th, 0)); // not applying is wrong — it is applicable
}

test "conflict blocks default" {
    // Fact: ¬a. Default: : a / a  cannot apply.
    const a = Literal.pos(0);
    const na = Literal.n(0);
    const d = Default{
        .prereq = &[_]Literal{},
        .justifications = &[_]Literal{a},
        .consequent = &[_]Literal{a},
    };
    const th = Theory{ .facts = &[_]Literal{na}, .defaults = &[_]Default{d} };
    try std.testing.expect(isExtension(&th, 0));
    try std.testing.expect(!isExtension(&th, 1));
}
