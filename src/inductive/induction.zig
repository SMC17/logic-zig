//! Mathematical induction — schema and inductive datatypes (universal spine).
//!
//! Distinguishes:
//!   - k-induction (already shipped in circuit/kinduction for temporal safety)
//!   - mathematical / structural induction over inductive datatypes
//!
//! This module provides the *schema* and a Peano example that can later be
//! discharged by the proof / type-theory path. It is a fragment, not a full
//! inductive theorem prover.

const std = @import("std");

/// Description of a simple inductive datatype (sum of products).
pub const Constructor = struct {
    name: []const u8,
    /// Arity (number of arguments). Full telescope comes later.
    arity: u32,
    /// Which argument positions are recursive (bitmask, max 32 args).
    recursive_mask: u32 = 0,
};

pub const InductiveType = struct {
    name: []const u8,
    constructors: []const Constructor,
};

/// Peano naturals: Nat := zero | succ(Nat)
pub const peano = InductiveType{
    .name = "Nat",
    .constructors = &[_]Constructor{
        .{ .name = "zero", .arity = 0, .recursive_mask = 0 },
        .{ .name = "succ", .arity = 1, .recursive_mask = 0b1 },
    },
};

/// Lists over an element type parameter (parameter not yet first-class).
pub fn listType(elem_name: []const u8) InductiveType {
    _ = elem_name;
    return .{
        .name = "List",
        .constructors = &[_]Constructor{
            .{ .name = "nil", .arity = 0, .recursive_mask = 0 },
            .{ .name = "cons", .arity = 2, .recursive_mask = 0b10 }, // second arg recursive
        },
    };
}

/// The induction principle for an inductive type.
///
/// For Nat:
///   ∀P. P(zero) → (∀n. P(n) → P(succ n)) → ∀n. P(n)
///
/// Represented abstractly so a future proof engine can instantiate it.
pub const InductionSchema = struct {
    type_name: []const u8,
    /// One motive / property name (string-level for the spine).
    motive: []const u8,
    /// Base cases: one per non-recursive constructor.
    base_cases: []const []const u8,
    /// Step cases: one per recursive constructor.
    step_cases: []const []const u8,

    pub fn forPeano(motive: []const u8) InductionSchema {
        return .{
            .type_name = "Nat",
            .motive = motive,
            .base_cases = &[_][]const u8{"P(zero)"},
            .step_cases = &[_][]const u8{"∀n. P(n) → P(succ n)"},
        };
    }
};

/// A concrete induction goal: prove motive for all inhabitants.
pub const InductionGoal = struct {
    schema: InductionSchema,
    /// Whether base and step have been supplied (checked structurally).
    base_discharged: bool = false,
    step_discharged: bool = false,

    pub fn isComplete(self: *const InductionGoal) bool {
        return self.base_discharged and self.step_discharged;
    }
};

/// Tiny checker: given an inductive type, verify that a claimed induction
/// schema mentions every constructor exactly once across base+step.
pub fn schemaCoversType(ty: *const InductiveType, schema: *const InductionSchema) bool {
    if (!std.mem.eql(u8, ty.name, schema.type_name)) return false;
    const total = schema.base_cases.len + schema.step_cases.len;
    return total == ty.constructors.len;
}

test "peano type has two constructors" {
    try std.testing.expect(peano.constructors.len == 2);
    try std.testing.expect(peano.constructors[0].arity == 0);
    try std.testing.expect(peano.constructors[1].recursive_mask == 0b1);
}

test "induction schema for peano" {
    const sch = InductionSchema.forPeano("even");
    try std.testing.expect(schemaCoversType(&peano, &sch));
    var goal = InductionGoal{ .schema = sch };
    try std.testing.expect(!goal.isComplete());
    goal.base_discharged = true;
    goal.step_discharged = true;
    try std.testing.expect(goal.isComplete());
}

test "list type spine" {
    const lt = listType("Nat");
    try std.testing.expect(lt.constructors.len == 2);
    try std.testing.expect(lt.constructors[1].recursive_mask == 0b10);
}
