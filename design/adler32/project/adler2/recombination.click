import click::integer;

// Bounds for the original Adler32::compute lane recombination expressions.
// These conditional arithmetic lemmas do not establish the loop invariants.
// The unchanged Rust source and Charon import are not modified.

theorem adler_recombine_difference(a: uint32) {
    requires a < 65521u32;
    ensures to_integer(65521u32 - a) == 65521 - to_integer(a)
        and 0 <= to_integer(65521u32 - a)
        and to_integer(65521u32 - a) <= 65521
        and to_integer(65521u32 - a) <= to_integer(65521u32) by {
        have a <= 65521u32 by solve() using { a < 65521u32; };
        have to_integer(65521u32 - a) == to_integer(65521u32) - to_integer(a);
        have 0 <= to_integer(a);
        have to_integer(65521u32 - a) == 65521 - to_integer(a) by solve() using { to_integer(65521u32 - a) == to_integer(65521u32) - to_integer(a); };
        have 0 <= to_integer(65521u32 - a) by {
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a));
            solve() using { to_integer(a) <= 65521; };
        }
        have to_integer(65521u32 - a) <= 65521 by {
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a));
            solve() using { 0 <= to_integer(a); };
        }
        assumption();
    }
}

theorem adler_recombine_lane_1(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + (65521u32 - a)) == to_integer(b) + (65521 - to_integer(a)) * 1
        and to_integer(b + (65521u32 - a)) <= 327601
        and to_integer((b as int64 + (65521u32 - a) as int64)) <= to_integer(4294967295i64) by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; };
        have to_integer(b) + to_integer(65521u32 - a) <= 4294967295 by solve() using { to_integer(b) <= 262080; to_integer(65521u32 - a) <= 65521; };
        have to_integer(b as int64 + (65521u32 - a) as int64) <= 4294967295;
        have b <= 4294967295u32 - to_integer(65521u32 - a);
        have to_integer(b + (65521u32 - a)) == to_integer(b) + to_integer((65521u32 - a));
        have to_integer(b + (65521u32 - a)) <= 327601 by { rewrite(to_integer(b + (65521u32 - a)) == to_integer(b) + to_integer(65521u32 - a)); solve() using { to_integer(b) <= 262080; to_integer(65521u32 - a) <= 65521; }; }
        have to_integer(b + (65521u32 - a)) == to_integer(b) + (65521 - to_integer(a)) * 1 by {
            rewrite(to_integer(b + (65521u32 - a)) == to_integer(b) + to_integer(65521u32 - a));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); solve() using {};
        }
        assumption();
    }
}

theorem adler_recombine_lane_2(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + (65521 - to_integer(a)) * 2
        and to_integer(b + ((65521u32 - a) * 2u32)) <= 393122
        and to_integer((b as int64 + ((65521u32 - a) * 2u32) as int64)) <= to_integer(4294967295i64) by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; };
        have to_integer(65521u32 - a) <= to_integer(4294967295u32 / 2u32) by solve() using { to_integer(65521u32 - a) <= to_integer(65521u32); };
        have 2u32 == 0u32 or to_integer(65521u32 - a) <= to_integer(4294967295u32 / 2u32) by assumption();
        apply(integer::uint32_multiply_to_integer(65521u32 - a, 2u32)) using { 2u32 == 0u32 or to_integer(65521u32 - a) <= to_integer(4294967295u32 / 2u32); };
        have to_integer((65521u32 - a) * 2u32) == (65521 - to_integer(a)) * 2 by {
            rewrite(to_integer((65521u32 - a) * 2u32) == to_integer(65521u32 - a) * to_integer(2u32));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); solve() using {};
        }
        have to_integer((65521u32 - a) * 2u32) <= 131042 by { rewrite(to_integer((65521u32 - a) * 2u32) == to_integer(65521u32 - a) * 2); solve() using { to_integer(65521u32 - a) <= 65521; }; }
        have to_integer(b) + to_integer((65521u32 - a) * 2u32) <= 4294967295 by solve() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 2u32) <= 131042; };
        have to_integer(b as int64 + ((65521u32 - a) * 2u32) as int64) <= 4294967295;
        have b <= 4294967295u32 - to_integer((65521u32 - a) * 2u32);
        have to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + to_integer(((65521u32 - a) * 2u32));
        have to_integer(b + ((65521u32 - a) * 2u32)) <= 393122 by { rewrite(to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + to_integer((65521u32 - a) * 2u32)); solve() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 2u32) <= 131042; }; }
        have to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + (65521 - to_integer(a)) * 2 by {
            rewrite(to_integer(b + ((65521u32 - a) * 2u32)) == to_integer(b) + to_integer((65521u32 - a) * 2u32));
            rewrite(to_integer((65521u32 - a) * 2u32) == (65521 - to_integer(a)) * 2); solve() using {};
        }
        assumption();
    }
}

theorem adler_recombine_lane_3(a: uint32, b: uint32) {
    requires a < 65521u32;
    requires to_integer(b) <= 262080;
    ensures to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + (65521 - to_integer(a)) * 3
        and to_integer(b + ((65521u32 - a) * 3u32)) <= 458643
        and to_integer((b as int64 + ((65521u32 - a) * 3u32) as int64)) <= to_integer(4294967295i64) by {
        apply(adler_recombine_difference(a)) using { a < 65521u32; };
        have to_integer(65521u32 - a) <= to_integer(4294967295u32 / 3u32) by solve() using { to_integer(65521u32 - a) <= to_integer(65521u32); };
        have 3u32 == 0u32 or to_integer(65521u32 - a) <= to_integer(4294967295u32 / 3u32) by assumption();
        apply(integer::uint32_multiply_to_integer(65521u32 - a, 3u32)) using { 3u32 == 0u32 or to_integer(65521u32 - a) <= to_integer(4294967295u32 / 3u32); };
        have to_integer((65521u32 - a) * 3u32) == (65521 - to_integer(a)) * 3 by {
            rewrite(to_integer((65521u32 - a) * 3u32) == to_integer(65521u32 - a) * to_integer(3u32));
            rewrite(to_integer(65521u32 - a) == 65521 - to_integer(a)); solve() using {};
        }
        have to_integer((65521u32 - a) * 3u32) <= 196563 by { rewrite(to_integer((65521u32 - a) * 3u32) == to_integer(65521u32 - a) * 3); solve() using { to_integer(65521u32 - a) <= 65521; }; }
        have to_integer(b) + to_integer((65521u32 - a) * 3u32) <= 4294967295 by solve() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 3u32) <= 196563; };
        have to_integer(b as int64 + ((65521u32 - a) * 3u32) as int64) <= 4294967295;
        have b <= 4294967295u32 - to_integer((65521u32 - a) * 3u32);
        have to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + to_integer(((65521u32 - a) * 3u32));
        have to_integer(b + ((65521u32 - a) * 3u32)) <= 458643 by { rewrite(to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + to_integer((65521u32 - a) * 3u32)); solve() using { to_integer(b) <= 262080; to_integer((65521u32 - a) * 3u32) <= 196563; }; }
        have to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + (65521 - to_integer(a)) * 3 by {
            rewrite(to_integer(b + ((65521u32 - a) * 3u32)) == to_integer(b) + to_integer((65521u32 - a) * 3u32));
            rewrite(to_integer((65521u32 - a) * 3u32) == (65521 - to_integer(a)) * 3); solve() using {};
        }
        assumption();
    }
}
