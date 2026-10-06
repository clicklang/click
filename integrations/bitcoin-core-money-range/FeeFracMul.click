verifying "bitcoin-src/src/util/feefrac.h";

int128 FeeFrac_Mul(int64 a, int32 b) {
    requires -9223372036854775808 <= to_integer(a);
    requires to_integer(a) <= 9223372036854775807;
    requires -2147483648 <= to_integer(b);
    requires to_integer(b) <= 2147483647;
    ensures to_integer(result) == to_integer(a) * to_integer(b);
} by {
    have -170141183460469231731687303715884105728 <= to_integer(a) * to_integer(b) by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= to_integer(a) => -9223372036854775808 <= to_integer(a);
            premise 1: to_integer(a) <= 9223372036854775807 => to_integer(a) <= 9223372036854775807;
            premise 2: -2147483648 <= to_integer(b) => -2147483648 <= to_integer(b);
            premise 3: to_integer(b) <= 2147483647 => to_integer(b) <= 2147483647;
            integer_product_bounds bounds [0, 1, 2, 3] => -170141183460469231731687303715884105728 <= to_integer(a) * to_integer(b);
            conclusion 0;
        }
    }
    have to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727 by {
        arithmetic_certificate special {
            premise 0: -9223372036854775808 <= to_integer(a) => -9223372036854775808 <= to_integer(a);
            premise 1: to_integer(a) <= 9223372036854775807 => to_integer(a) <= 9223372036854775807;
            premise 2: -2147483648 <= to_integer(b) => -2147483648 <= to_integer(b);
            premise 3: to_integer(b) <= 2147483647 => to_integer(b) <= 2147483647;
            integer_product_bounds bounds [0, 1, 2, 3] => to_integer(a) * to_integer(b) <= 170141183460469231731687303715884105727;
            conclusion 0;
        }
    }
    execute();
    simp();
}
