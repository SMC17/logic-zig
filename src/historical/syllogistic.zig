//! Aristotelian syllogistic — categorical propositions and valid moods.
//!
//! Four forms (square of opposition):
//!   A: All S are P     (universal affirmative)
//!   E: No S are P      (universal negative)
//!   I: Some S are P    (particular affirmative)
//!   O: Some S are not P (particular negative)
//!
//! Figures 1–4 by middle-term placement; moods named Barbara, Celarent, …
//! Fragment: classification + validity table for the 24 traditionally valid
//! moods (including weakened). Not a full term-logic proof engine.

const std = @import("std");

pub const Quantity = enum { universal, particular };
pub const Quality = enum { affirmative, negative };

pub const Form = enum {
    /// All S are P
    A,
    /// No S are P
    E,
    /// Some S are P
    I,
    /// Some S are not P
    O,

    pub fn quantity(self: Form) Quantity {
        return switch (self) {
            .A, .E => .universal,
            .I, .O => .particular,
        };
    }

    pub fn quality(self: Form) Quality {
        return switch (self) {
            .A, .I => .affirmative,
            .E, .O => .negative,
        };
    }

    pub fn fromLetter(c: u8) ?Form {
        return switch (c) {
            'A', 'a' => .A,
            'E', 'e' => .E,
            'I', 'i' => .I,
            'O', 'o' => .O,
            else => null,
        };
    }
};

/// Figure by position of middle term M relative to major P and minor S.
///   Fig 1: M–P / S–M
///   Fig 2: P–M / S–M
///   Fig 3: M–P / M–S
///   Fig 4: P–M / M–S
pub const Figure = enum(u8) { fig1 = 1, fig2 = 2, fig3 = 3, fig4 = 4 };

pub const Mood = struct {
    major: Form,
    minor: Form,
    conclusion: Form,
    figure: Figure,

    pub fn nameLetters(self: Mood) [3]u8 {
        const letter = struct {
            fn f(form: Form) u8 {
                return switch (form) {
                    .A => 'A',
                    .E => 'E',
                    .I => 'I',
                    .O => 'O',
                };
            }
        }.f;
        return .{ letter(self.major), letter(self.minor), letter(self.conclusion) };
    }
};

/// Traditionally valid moods (Aristotle + medieval, including subalterns).
const valid_table = [_]struct { letters: []const u8, figure: Figure, name: []const u8 }{
    // Figure 1
    .{ .letters = "AAA", .figure = .fig1, .name = "Barbara" },
    .{ .letters = "EAE", .figure = .fig1, .name = "Celarent" },
    .{ .letters = "AII", .figure = .fig1, .name = "Darii" },
    .{ .letters = "EIO", .figure = .fig1, .name = "Ferio" },
    .{ .letters = "AAI", .figure = .fig1, .name = "Barbari" },
    .{ .letters = "EAO", .figure = .fig1, .name = "Celaront" },
    // Figure 2
    .{ .letters = "EAE", .figure = .fig2, .name = "Cesare" },
    .{ .letters = "AEE", .figure = .fig2, .name = "Camestres" },
    .{ .letters = "EIO", .figure = .fig2, .name = "Festino" },
    .{ .letters = "AOO", .figure = .fig2, .name = "Baroco" },
    .{ .letters = "EAO", .figure = .fig2, .name = "Cesaro" },
    .{ .letters = "AEO", .figure = .fig2, .name = "Camestrop" },
    // Figure 3
    .{ .letters = "AAI", .figure = .fig3, .name = "Darapti" },
    .{ .letters = "IAI", .figure = .fig3, .name = "Disamis" },
    .{ .letters = "AII", .figure = .fig3, .name = "Datisi" },
    .{ .letters = "EAO", .figure = .fig3, .name = "Felapton" },
    .{ .letters = "OAO", .figure = .fig3, .name = "Bocardo" },
    .{ .letters = "EIO", .figure = .fig3, .name = "Ferison" },
    // Figure 4
    .{ .letters = "AAI", .figure = .fig4, .name = "Bramantip" },
    .{ .letters = "AEE", .figure = .fig4, .name = "Camenes" },
    .{ .letters = "IAI", .figure = .fig4, .name = "Dimaris" },
    .{ .letters = "EAO", .figure = .fig4, .name = "Fesapo" },
    .{ .letters = "EIO", .figure = .fig4, .name = "Fresison" },
    .{ .letters = "AEO", .figure = .fig4, .name = "Camenop" },
};

pub fn isValid(mood: Mood) bool {
    const letters = mood.nameLetters();
    for (valid_table) |row| {
        if (row.figure == mood.figure and
            row.letters[0] == letters[0] and
            row.letters[1] == letters[1] and
            row.letters[2] == letters[2]) return true;
    }
    return false;
}

pub fn moodName(mood: Mood) ?[]const u8 {
    const letters = mood.nameLetters();
    for (valid_table) |row| {
        if (row.figure == mood.figure and
            row.letters[0] == letters[0] and
            row.letters[1] == letters[1] and
            row.letters[2] == letters[2]) return row.name;
    }
    return null;
}

pub fn validCount() usize {
    return valid_table.len;
}

test "barbara valid" {
    const m = Mood{ .major = .A, .minor = .A, .conclusion = .A, .figure = .fig1 };
    try std.testing.expect(isValid(m));
    try std.testing.expectEqualStrings("Barbara", moodName(m).?);
}

test "invalid mood rejected" {
    const m = Mood{ .major = .A, .minor = .A, .conclusion = .E, .figure = .fig1 };
    try std.testing.expect(!isValid(m));
}

test "baroco figure 2" {
    const m = Mood{ .major = .A, .minor = .O, .conclusion = .O, .figure = .fig2 };
    try std.testing.expect(isValid(m));
    try std.testing.expectEqualStrings("Baroco", moodName(m).?);
}

test "twenty four valid moods" {
    try std.testing.expect(validCount() == 24);
}
