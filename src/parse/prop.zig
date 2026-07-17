//! Recursive-descent parser for propositional formulas.
//!
//! Grammar (low → high precedence):
//!   formula  := iff
//!   iff      := implies (('<->'|'<=>'|'iff') implies)*
//!   implies  := or (('->'|'=>'|'implies') or)*   // right-assoc via loop fold right
//!   or       := xor (('|'|'||'|'or'|'v') xor)*
//!   xor      := and (('^'|'xor') and)*
//!   and      := unary (('&'|'&&'|'and') unary)*
//!   unary    := ('!'|'~'|'not'|'-') unary | primary
//!   primary  := 'true'|'false'|'1'|'0'|ident|'(' formula ')'
//!
//! Identifiers: [A-Za-z_][A-Za-z0-9_]*

const std = @import("std");
const expr_mod = @import("../ir/expr.zig");
const ExprPool = expr_mod.ExprPool;
const ExprId = expr_mod.ExprId;

pub const ParseError = error{
    UnexpectedToken,
    UnexpectedEof,
    InvalidCharacter,
    EmptyInput,
} || std.mem.Allocator.Error;

pub fn parse(pool: *ExprPool, source: []const u8) ParseError!ExprId {
    var p = Parser{
        .pool = pool,
        .src = source,
        .i = 0,
    };
    p.skipWs();
    if (p.i >= p.src.len) return error.EmptyInput;
    const e = try p.parseIff();
    p.skipWs();
    if (p.i < p.src.len) return error.UnexpectedToken;
    return e;
}

const Parser = struct {
    pool: *ExprPool,
    src: []const u8,
    i: usize,

    fn skipWs(self: *Parser) void {
        while (self.i < self.src.len) {
            const c = self.src[self.i];
            if (c == ' ' or c == '\t' or c == '\n' or c == '\r') {
                self.i += 1;
            } else if (c == '/' and self.i + 1 < self.src.len and self.src[self.i + 1] == '/') {
                self.i += 2;
                while (self.i < self.src.len and self.src[self.i] != '\n') self.i += 1;
            } else break;
        }
    }

    fn peek(self: *Parser) ?u8 {
        if (self.i >= self.src.len) return null;
        return self.src[self.i];
    }

    fn startsWith(self: *Parser, s: []const u8) bool {
        if (self.i + s.len > self.src.len) return false;
        return std.mem.eql(u8, self.src[self.i .. self.i + s.len], s);
    }

    /// Keyword match only if not followed by ident char.
    fn matchKeyword(self: *Parser, kw: []const u8) bool {
        if (!self.startsWith(kw)) return false;
        const after = self.i + kw.len;
        if (after < self.src.len and isIdentCont(self.src[after])) return false;
        self.i = after;
        self.skipWs();
        return true;
    }

    fn matchOp(self: *Parser, op: []const u8) bool {
        if (!self.startsWith(op)) return false;
        self.i += op.len;
        self.skipWs();
        return true;
    }

    fn parseIff(self: *Parser) ParseError!ExprId {
        var left = try self.parseImplies();
        while (true) {
            self.skipWs();
            if (self.matchOp("<->") or self.matchOp("<=>") or self.matchKeyword("iff")) {
                const right = try self.parseImplies();
                left = try self.pool.mkIff(left, right);
            } else break;
        }
        return left;
    }

    fn parseImplies(self: *Parser) ParseError!ExprId {
        // Collect chain a -> b -> c as right-assoc: a -> (b -> c)
        var nodes: std.ArrayList(ExprId) = .empty;
        defer nodes.deinit(self.pool.allocator);
        try nodes.append(self.pool.allocator, try self.parseOr());
        while (true) {
            self.skipWs();
            if (self.matchOp("->") or self.matchOp("=>") or self.matchKeyword("implies")) {
                try nodes.append(self.pool.allocator, try self.parseOr());
            } else break;
        }
        var i = nodes.items.len;
        var acc = nodes.items[i - 1];
        while (i > 1) {
            i -= 1;
            acc = try self.pool.mkImplies(nodes.items[i - 1], acc);
        }
        return acc;
    }

    fn parseOr(self: *Parser) ParseError!ExprId {
        var left = try self.parseXor();
        while (true) {
            self.skipWs();
            if (self.matchOp("||") or self.matchOp("|") or self.matchKeyword("or") or self.matchKeyword("v")) {
                const right = try self.parseXor();
                left = try self.pool.mkOr(left, right);
            } else break;
        }
        return left;
    }

    fn parseXor(self: *Parser) ParseError!ExprId {
        var left = try self.parseAnd();
        while (true) {
            self.skipWs();
            if (self.matchOp("^") or self.matchKeyword("xor")) {
                const right = try self.parseAnd();
                left = try self.pool.mkXor(left, right);
            } else break;
        }
        return left;
    }

    fn parseAnd(self: *Parser) ParseError!ExprId {
        var left = try self.parseUnary();
        while (true) {
            self.skipWs();
            if (self.matchOp("&&") or self.matchOp("&") or self.matchKeyword("and")) {
                const right = try self.parseUnary();
                left = try self.pool.mkAnd(left, right);
            } else break;
        }
        return left;
    }

    fn parseUnary(self: *Parser) ParseError!ExprId {
        self.skipWs();
        if (self.matchOp("!") or self.matchOp("~") or self.matchKeyword("not") or self.matchOp("¬")) {
            return try self.pool.mkNot(try self.parseUnary());
        }
        // Unary minus as negation only when followed by ident/paren (not number alone handled in primary)
        if (self.peek() == '-') {
            const next = if (self.i + 1 < self.src.len) self.src[self.i + 1] else 0;
            if (next == '(' or isIdentStart(next)) {
                self.i += 1;
                self.skipWs();
                return try self.pool.mkNot(try self.parseUnary());
            }
        }
        return try self.parsePrimary();
    }

    fn parsePrimary(self: *Parser) ParseError!ExprId {
        self.skipWs();
        if (self.i >= self.src.len) return error.UnexpectedEof;

        if (self.matchOp("(")) {
            const e = try self.parseIff();
            self.skipWs();
            if (!self.matchOp(")")) return error.UnexpectedToken;
            return e;
        }

        if (self.matchKeyword("true") or self.matchKeyword("True") or self.matchKeyword("TRUE")) {
            return self.pool.mkTrue();
        }
        if (self.matchKeyword("false") or self.matchKeyword("False") or self.matchKeyword("FALSE")) {
            return self.pool.mkFalse();
        }

        // Lone 0/1 as constants if not part of longer ident.
        if (self.peek() == '0' or self.peek() == '1') {
            const c = self.peek().?;
            const after = self.i + 1;
            if (after >= self.src.len or !isIdentCont(self.src[after])) {
                self.i += 1;
                self.skipWs();
                return self.pool.mkConst(c == '1');
            }
        }

        if (self.peek()) |c| {
            if (isIdentStart(c)) {
                const start = self.i;
                self.i += 1;
                while (self.i < self.src.len and isIdentCont(self.src[self.i])) self.i += 1;
                const name = self.src[start..self.i];
                self.skipWs();
                return try self.pool.mkVarNamed(name);
            }
        }
        return error.UnexpectedToken;
    }
};

fn isIdentStart(c: u8) bool {
    return (c >= 'A' and c <= 'Z') or (c >= 'a' and c <= 'z') or c == '_';
}

fn isIdentCont(c: u8) bool {
    return isIdentStart(c) or (c >= '0' and c <= '9');
}

test "parse modus ponens shape" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const e = try parse(&pool, "(a -> b) & a");
    _ = e;
    const taut = try parse(&pool, "a | !a");
    try std.testing.expect(pool.tag(taut) == .or_ or taut == .true_);
}

test "parse precedence" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    // a | b & c  ==  a | (b & c)
    const e = try parse(&pool, "a | b & c");
    try std.testing.expect(pool.tag(e) == .or_);
}

test "parse constants and xor" {
    var pool = try ExprPool.init(std.testing.allocator);
    defer pool.deinit();
    const e = try parse(&pool, "true ^ false");
    try std.testing.expect(e == .true_ or pool.tag(e) == .xor or e == .true_);
    // true ^ false simplifies in mkXor to not false = true
    try std.testing.expect(e == .true_);
}
