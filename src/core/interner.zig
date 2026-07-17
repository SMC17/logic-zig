//! Dense string interner: symbol bytes live once; IDs are u32 indices.

const std = @import("std");

pub const SymbolId = enum(u32) {
    _,

    pub fn index(self: SymbolId) u32 {
        return @intFromEnum(self);
    }

    pub fn fromIndex(i: u32) SymbolId {
        return @enumFromInt(i);
    }
};

pub const Interner = struct {
    allocator: std.mem.Allocator,
    bytes: std.ArrayList(u8) = .empty,
    /// offsets[i]..offsets[i+1] is symbol i (offsets has len = n+1).
    offsets: std.ArrayList(u32) = .empty,
    map: std.StringHashMapUnmanaged(SymbolId) = .{},

    pub fn init(allocator: std.mem.Allocator) Interner {
        return .{ .allocator = allocator };
    }

    pub fn deinit(self: *Interner) void {
        self.map.deinit(self.allocator);
        self.bytes.deinit(self.allocator);
        self.offsets.deinit(self.allocator);
        self.* = undefined;
    }

    pub fn count(self: *const Interner) u32 {
        return @intCast(if (self.offsets.items.len == 0) 0 else self.offsets.items.len - 1);
    }

    pub fn intern(self: *Interner, name: []const u8) !SymbolId {
        if (self.map.get(name)) |id| return id;

        if (self.offsets.items.len == 0) {
            try self.offsets.append(self.allocator, 0);
        }
        const start: u32 = @intCast(self.bytes.items.len);
        try self.bytes.appendSlice(self.allocator, name);
        const end: u32 = @intCast(self.bytes.items.len);
        try self.offsets.append(self.allocator, end);

        const id = SymbolId.fromIndex(@intCast(self.offsets.items.len - 2));
        // Key must point into our stable storage after append.
        const key = self.bytes.items[start..end];
        try self.map.put(self.allocator, key, id);
        return id;
    }

    pub fn get(self: *const Interner, id: SymbolId) []const u8 {
        const i = id.index();
        const start = self.offsets.items[i];
        const end = self.offsets.items[i + 1];
        return self.bytes.items[start..end];
    }
};

test "interner dedup" {
    var intern = Interner.init(std.testing.allocator);
    defer intern.deinit();
    const a = try intern.intern("alpha");
    const b = try intern.intern("beta");
    const a2 = try intern.intern("alpha");
    try std.testing.expect(a == a2);
    try std.testing.expect(a != b);
    try std.testing.expectEqualStrings("alpha", intern.get(a));
    try std.testing.expectEqualStrings("beta", intern.get(b));
    try std.testing.expect(intern.count() == 2);
}
