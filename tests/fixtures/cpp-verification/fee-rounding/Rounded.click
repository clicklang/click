verifying "round.cpp";
int64 rounded(int128 n, int32 d, bool round_down) {
    requires -100 <= to_integer(n);
    requires to_integer(n) <= 100;
    requires d > 0;
    requires d <= 100;
    ensures 0 == 0;
} by {
    have 1 <= d by { arithmetic() using { d > 0; } }
    apply(int32_less_equal_to_integer(1, d));
    apply(int32_less_equal_to_integer(d, 100));
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
    have -100 <= truncating_quotient(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n) => -100 <= to_integer(n);
        premise 1: to_integer(n) <= 100 => to_integer(n) <= 100;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => -100 <= truncating_quotient(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have truncating_quotient(to_integer(n), to_integer(d)) <= 100 by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n) => -100 <= to_integer(n);
        premise 1: to_integer(n) <= 100 => to_integer(n) <= 100;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => truncating_quotient(to_integer(n), to_integer(d)) <= 100; conclusion 0;
    } }
    have -100 <= to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: -100 <= truncating_quotient(to_integer(n), to_integer(d)) => -100 <= truncating_quotient(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -100 <= to_integer(n / (int128)d); conclusion 0;
    } }
    have to_integer(n / (int128)d) <= 100 by { arithmetic_certificate special {
        premise 0: to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d)) => to_integer(n / (int128)d) == truncating_quotient(to_integer(n), to_integer(d));
        premise 1: truncating_quotient(to_integer(n), to_integer(d)) <= 100 => truncating_quotient(to_integer(n), to_integer(d)) <= 100;
        integer_relation_transport bounds [0, 1] => to_integer(n / (int128)d) <= 100; conclusion 0;
    } }
    have to_integer(quot) == to_integer(n / (int128)d) by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n / (int128)d) => -100 <= to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 100 => to_integer(n / (int128)d) <= 100;
        integer_cast_identity bounds [0, 1] => to_integer(quot) == to_integer(n / (int128)d); conclusion 0;
    } }
    have -100 <= to_integer(quot) by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: -100 <= to_integer(n / (int128)d) => -100 <= to_integer(n / (int128)d);
        integer_relation_transport bounds [0, 1] => -100 <= to_integer(quot); conclusion 0;
    } }
    have to_integer(quot) <= 100 by { arithmetic_certificate special {
        premise 0: to_integer(quot) == to_integer(n / (int128)d) => to_integer(quot) == to_integer(n / (int128)d);
        premise 1: to_integer(n / (int128)d) <= 100 => to_integer(n / (int128)d) <= 100;
        integer_relation_transport bounds [0, 1] => to_integer(quot) <= 100; conclusion 0;
    } }
    apply(int64_less_equal_of_to_integer(-100i64, quot));
    apply(int64_less_equal_of_to_integer(quot, 100i64));
    step();
    step();
    have -100 <= truncating_remainder(to_integer(n), to_integer(d)) by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n) => -100 <= to_integer(n);
        premise 1: to_integer(n) <= 100 => to_integer(n) <= 100;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => -100 <= truncating_remainder(to_integer(n), to_integer(d)); conclusion 0;
    } }
    have truncating_remainder(to_integer(n), to_integer(d)) <= 100 by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n) => -100 <= to_integer(n);
        premise 1: to_integer(n) <= 100 => to_integer(n) <= 100;
        premise 2: 1 <= to_integer(d) => 1 <= to_integer(d);
        premise 3: to_integer(d) <= 100 => to_integer(d) <= 100;
        integer_division_bounds bounds [0, 1, 2, 3] => truncating_remainder(to_integer(n), to_integer(d)) <= 100; conclusion 0;
    } }
    have -100 <= to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: -100 <= truncating_remainder(to_integer(n), to_integer(d)) => -100 <= truncating_remainder(to_integer(n), to_integer(d));
        integer_relation_transport bounds [0, 1] => -100 <= to_integer(n % (int128)d); conclusion 0;
    } }
    have to_integer(n % (int128)d) <= 100 by { arithmetic_certificate special {
        premise 0: to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d)) => to_integer(n % (int128)d) == truncating_remainder(to_integer(n), to_integer(d));
        premise 1: truncating_remainder(to_integer(n), to_integer(d)) <= 100 => truncating_remainder(to_integer(n), to_integer(d)) <= 100;
        integer_relation_transport bounds [0, 1] => to_integer(n % (int128)d) <= 100; conclusion 0;
    } }
    have to_integer(mod) == to_integer(n % (int128)d) by { arithmetic_certificate special {
        premise 0: -100 <= to_integer(n % (int128)d) => -100 <= to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 100 => to_integer(n % (int128)d) <= 100;
        integer_cast_identity bounds [0, 1] => to_integer(mod) == to_integer(n % (int128)d); conclusion 0;
    } }
    have -100 <= to_integer(mod) by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: -100 <= to_integer(n % (int128)d) => -100 <= to_integer(n % (int128)d);
        integer_relation_transport bounds [0, 1] => -100 <= to_integer(mod); conclusion 0;
    } }
    have to_integer(mod) <= 100 by { arithmetic_certificate special {
        premise 0: to_integer(mod) == to_integer(n % (int128)d) => to_integer(mod) == to_integer(n % (int128)d);
        premise 1: to_integer(n % (int128)d) <= 100 => to_integer(n % (int128)d) <= 100;
        integer_relation_transport bounds [0, 1] => to_integer(mod) <= 100; conclusion 0;
    } }
    apply(int32_less_equal_of_to_integer(-100, mod));
    apply(int32_less_equal_of_to_integer(mod, 100));
    execute(); simp();
}
