verifying "bitcoin-src/src/util/feefrac.h";
int64 FeeFrac_Div(int128 n, int32 d, bool round_down) {
    requires -9223372036854775806 <= to_integer(n);
    requires to_integer(n) <= 9223372036854775806;
    requires d > 0;
    requires d <= 2147483647;
    ensures -9223372036854775807 <= to_integer(result);
    ensures to_integer(result) <= 9223372036854775807;
    ensures -9223372036854775807i64 <= result;
    ensures result <= 9223372036854775807i64;
} by {
    have 1 <= d by { arithmetic() using { d > 0; } }
    apply(int32_less_equal_to_integer(1, d));
    apply(int32_less_equal_to_integer(d, 2147483647));
    have to_integer(d) != 0 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != 0; conclusion 0;
    } }
    have to_integer(d) != -1 by { arithmetic_certificate special {
        premise 0: 1 <= to_integer(d) => 1 <= to_integer(d);
        integer_bound_exclusion bounds [0] => to_integer(d) != -1; conclusion 0;
    } }
    step();
    step();
    step();
    have -9223372036854775806 <= truncating_quotient(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: -9223372036854775806 <= to_integer(n) => -9223372036854775806 <= to_integer(n);
        premise 1: to_integer(n) <= 9223372036854775806 => to_integer(n) <= 9223372036854775806;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 2147483647 => to_integer(d) <= 2147483647;
        integer_division_bounds bounds [0, 1, 2, 3] => -9223372036854775806 <= truncating_quotient(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775806 by { arithmetic_certificate special {
        premise 0: -9223372036854775806 <= to_integer(n) => -9223372036854775806 <= to_integer(n);
        premise 1: to_integer(n) <= 9223372036854775806 => to_integer(n) <= 9223372036854775806;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 2147483647 => to_integer(d) <= 2147483647;
        integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775806; conclusion 0;
    } }
    have -9223372036854775806 <= to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: -9223372036854775806 <= truncating_quotient(to_integer(n), to_integer(d)) => -9223372036854775806 <= truncating_quotient(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -9223372036854775806 <= to_integer(n / (int128)d); conclusion 0;
    } }
    have to_integer(n / (int128)d) <= 9223372036854775806 by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775806 => truncating_quotient(to_integer(n), to_integer(d)) <= 9223372036854775806;
        integer_relation_transport bounds [0, 1] => to_integer(n / (int128)d) <= 9223372036854775806; conclusion 0;
    } }
    have to_integer(quot) == to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: -9223372036854775806 <= to_integer(n / (int128)d) => -9223372036854775806 <= to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 9223372036854775806 => to_integer(n / (int128)d) <= 9223372036854775806;
        integer_cast_identity bounds [0, 1] => to_integer(quot) == to_integer(n / (int128)d); conclusion 0;
    } }
    have -9223372036854775806 <= to_integer(quot) by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: -9223372036854775806 <= to_integer(n / (int128)d) => -9223372036854775806 <= to_integer(n / (int128)d);
        integer_relation_transport bounds [0, 1] => -9223372036854775806 <= to_integer(quot); conclusion 0;
    } }
    have to_integer(quot) <= 9223372036854775806 by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 9223372036854775806 => to_integer(n / (int128)d) <= 9223372036854775806;
        integer_relation_transport bounds [0, 1] => to_integer(quot) <= 9223372036854775806; conclusion 0;
    } }
    apply(int64_less_equal_of_to_integer(-9223372036854775806i64, quot));
    apply(int64_less_equal_of_to_integer(quot, 9223372036854775806i64));
    step();
    step();
    have -2147483646 <= truncating_remainder(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: -9223372036854775806 <= to_integer(n) => -9223372036854775806 <= to_integer(n);
        premise 1: to_integer(n) <= 9223372036854775806 => to_integer(n) <= 9223372036854775806;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 2147483647 => to_integer(d) <= 2147483647;
        integer_division_bounds bounds [0, 1, 2, 3] => -2147483646 <= truncating_remainder(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646 by { arithmetic_certificate special {
        premise 0: -9223372036854775806 <= to_integer(n) => -9223372036854775806 <= to_integer(n);
        premise 1: to_integer(n) <= 9223372036854775806 => to_integer(n) <= 9223372036854775806;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 2147483647 => to_integer(d) <= 2147483647;
        integer_division_bounds bounds [0, 1, 2, 3] => truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646; conclusion 0;
    } }
    have -2147483646 <= to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: -2147483646 <= truncating_remainder(to_integer(n), to_integer(d)) => -2147483646 <= truncating_remainder(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -2147483646 <= to_integer(n % (int128)d); conclusion 0;
    } }
    have to_integer(n % (int128)d) <= 2147483646 by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646 => truncating_remainder(to_integer(n), to_integer(d)) <= 2147483646;
        integer_relation_transport bounds [0, 1] => to_integer(n % (int128)d) <= 2147483646; conclusion 0;
    } }
    have to_integer(mod) == to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: -2147483646 <= to_integer(n % (int128)d) => -2147483646 <= to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 2147483646 => to_integer(n % (int128)d) <= 2147483646;
        integer_cast_identity bounds [0, 1] => to_integer(mod) == to_integer(n % (int128)d); conclusion 0;
    } }
    have -2147483646 <= to_integer(mod) by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: -2147483646 <= to_integer(n % (int128)d) => -2147483646 <= to_integer(n % (int128)d);
        integer_relation_transport bounds [0, 1] => -2147483646 <= to_integer(mod); conclusion 0;
    } }
    have to_integer(mod) <= 2147483646 by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 2147483646 => to_integer(n % (int128)d) <= 2147483646;
        integer_relation_transport bounds [0, 1] => to_integer(mod) <= 2147483646; conclusion 0;
    } }
    apply(int32_less_equal_of_to_integer(-2147483646, mod));
    apply(int32_less_equal_of_to_integer(mod, 2147483646));
    have defined(quot + 0i64) by simp;
    have defined(quot + 1i64) by simp;
    have defined(quot + -1i64) by simp;
    apply(int64_add_to_integer(quot, 0i64));
    apply(int64_add_to_integer(quot, 1i64));
    apply(int64_add_to_integer(quot, -1i64));
    have -9223372036854775807 <= to_integer(quot + 0i64) by { arithmetic() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    have to_integer(quot + 0i64) <= 9223372036854775807 by { arithmetic() using {
        to_integer(quot + 0i64) == to_integer(quot) + 0;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    have -9223372036854775807 <= to_integer(quot + 1i64) by { arithmetic() using {
        to_integer(quot + 1i64) == to_integer(quot) + 1;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    have to_integer(quot + 1i64) <= 9223372036854775807 by { arithmetic() using {
        to_integer(quot + 1i64) == to_integer(quot) + 1;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    have -9223372036854775807 <= to_integer(quot + -1i64) by { arithmetic() using {
        to_integer(quot + -1i64) == to_integer(quot) + -1;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    have to_integer(quot + -1i64) <= 9223372036854775807 by { arithmetic() using {
        to_integer(quot + -1i64) == to_integer(quot) + -1;
        -9223372036854775806 <= to_integer(quot);
        to_integer(quot) <= 9223372036854775806;
    } }
    execute();
    have -9223372036854775807 <= to_integer(result) by simp;
    have to_integer(result) <= 9223372036854775807 by simp;
    apply(int64_less_equal_of_to_integer(-9223372036854775807i64, result));
    apply(int64_less_equal_of_to_integer(result, 9223372036854775807i64));
    simp();
}
