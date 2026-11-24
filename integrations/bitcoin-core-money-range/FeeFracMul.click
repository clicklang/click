verifying "bitcoin-src/src/util/feefrac.h";

static int128 FeeFrac::Mul(int64 a, int32 b) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(result) == to_integer(a) * to_integer(b);
} by {
    have -170141183460469231731687303715884105728 <= to_integer(a) * to_integer(b) by {
        close() using { -9223372036854775808 <= to_integer(a); to_integer(a) <= 9223372036854775807; -2147483648 <= to_integer(b); to_integer(b) <= 2147483647; };
    }
    have to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727 by {
        close() using { -9223372036854775808 <= to_integer(a); to_integer(a) <= 9223372036854775807; -2147483648 <= to_integer(b); to_integer(b) <= 2147483647; };
    }
}
