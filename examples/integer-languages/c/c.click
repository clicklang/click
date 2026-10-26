// The C side of the cross-language integer fixture
// (`tests/examples/integer_languages.rs`): the same claims as
// `../cpp/cpp.click` and `../rust/rust.click`. C verifies every case; a case
// it did not would be in `c.click-gap`.

import click::integer;

verifying "integers.c";

int32 add_i32(int32 a, int32 b) {
    requires -2147483648 <= a + b and a + b <= 2147483647;
    ensures result == a + b;
}

int32 sub_i32(int32 a, int32 b) {
    requires -2147483648 <= a - b and a - b <= 2147483647;
    ensures result == a - b;
}

int32 mul_i32(int32 a, int32 b) {
    requires -2147483648 <= a * b and a * b <= 2147483647;
    ensures result == a * b;
} by {
    step_until(function.exit);
    have to_integer(a * b) == to_integer(a) * to_integer(b) by {
        arithmetic_certificate rules {
            premise 0: -2147483648 <= to_integer(a) * to_integer(b) => -2147483648 <= to_integer(a) * to_integer(b);
            premise 1: to_integer(a) * to_integer(b) <= 2147483647 => to_integer(a) * to_integer(b) <= 2147483647;
            integer_operation_identity bounds [0, 1] => to_integer(a * b) == to_integer(a) * to_integer(b);
            conclusion 0;
        }
    };
    solve();
}

uint32 wrapping_add_u32(uint32 a, uint32 b) {
    ensures result == integer::uint32_wrapping_add(a, b);
}

uint32 wrapping_sub_u32(uint32 a, uint32 b) {
    ensures result == integer::uint32_wrapping_sub(a, b);
}

uint32 wrapping_mul_u32(uint32 a, uint32 b) {
    ensures result == integer::uint32_wrapping_mul(a, b);
}

uint32 above_int32_max() {
    ensures result == 4000000000u32;
    ensures result > 2147483647u32;
}

uint32 keep_above_int32_max(uint32 u) {
    ensures u > 2147483647u32 implies result == u;
    ensures u <= 2147483647u32 implies result == 0u32;
    ensures u == 4000000000u32 implies result == 4000000000u32;
}

int32 to_signed_i32(uint32 u) {
    ensures result == u as int32;
    ensures u == 4294967295u32 implies result == -1;
    ensures u == 2147483648u32 implies result == -2147483648;
}

uint32 to_unsigned_u32(int32 x) {
    ensures result == x as uint32;
    ensures x == -1 implies result == 4294967295u32;
    ensures result as int32 == x;
}

uint32 div_u32(uint32 a, uint32 b) {
    requires b != 0u32;
    ensures result == a / b;
    ensures (a == 4294967295u32 and b == 2u32) implies result == 2147483647u32;
}

uint32 rem_u32(uint32 a, uint32 b) {
    requires b != 0u32;
    ensures result == a % b;
    ensures (a == 4294967295u32 and b == 10u32) implies result == 5u32;
}

uint32 shr_u32(uint32 a, uint32 n) {
    requires n < 32u32;
    ensures result == a >> n;
    ensures (a == 2147483648u32 and n == 1u32) implies result == 1073741824u32;
}

int32 div_i32(int32 a, int32 b) {
    requires b != 0;
    requires a != -2147483648 or b != -1;
    ensures result == a / b;
    ensures (a == -7 and b == 2) implies result == -3;
    ensures (a == 7 and b == -2) implies result == -3;
}

int32 rem_i32(int32 a, int32 b) {
    requires b != 0;
    requires a != -2147483648 or b != -1;
    ensures result == a % b;
    ensures (a == -7 and b == 2) implies result == -1;
    ensures (a == 7 and b == -2) implies result == 1;
}

int32 shr_i32(int32 a, uint32 n) {
    requires n < 32u32;
    ensures result == a >> n;
    ensures (a == -8 and n == 1u32) implies result == -4;
}

uint8 narrow_u8(uint32 x) {
    ensures result as uint32 == (x & 255u32);
    ensures x == 4000000000u32 implies result == 0u8;
    ensures x == 300u32 implies result == 44u8;
}

int8 narrow_i8(int32 x) {
    ensures (-128 <= x and x <= 127) implies to_integer(result) == to_integer(x);
    ensures x == 200 implies to_integer(result) == -56;
    ensures x == -129 implies to_integer(result) == 127;
} by {
    if -128 <= x and x <= 127 {
        step_until(function.exit);
        have -128 <= to_integer(x);
        have to_integer(x) <= 127;
        have to_integer(result) == to_integer(x) by {
            arithmetic_certificate rules {
                premise 0: -128 <= to_integer(x) => -128 <= to_integer(x);
                premise 1: to_integer(x) <= 127 => to_integer(x) <= 127;
                integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(x);
                conclusion 0;
            }
        };
        solve();
    } else {
        step_until(function.exit);
        solve();
    }
}

uint8 narrow_u8_in_range(uint32 x) {
    requires x <= 255u32;
    ensures to_integer(result) == to_integer(x);
} by {
    step_until(function.exit);
    have 0 <= to_integer(x);
    have to_integer(x) <= 255;
    have to_integer(result) == to_integer(x) by {
        arithmetic_certificate rules {
            premise 0: 0 <= to_integer(x) => 0 <= to_integer(x);
            premise 1: to_integer(x) <= 255 => to_integer(x) <= 255;
            integer_cast_identity bounds [0, 1] => to_integer(result) == to_integer(x);
            conclusion 0;
        }
    };
}

int64 add_i64(int64 a, int64 b) {
    requires -9223372036854775808 <= a + b and a + b <= 9223372036854775807;
    ensures result == a + b;
}

uint64 wrapping_add_u64(uint64 a, uint64 b) {
    ensures result == integer::uint64_wrapping_add(a, b);
}

bool below_i32(int32 a, int32 b) {
    ensures result implies a < b;
    ensures a < b implies result;
    ensures (a == -2147483648 and b == 0) implies result;
} by {
    if a == -2147483648 and b == 0 { step_until(function.exit); solve(); }
    else { step_until(function.exit); solve(); }
}

bool below_u32(uint32 a, uint32 b) {
    ensures result implies a < b;
    ensures a < b implies result;
    ensures (a == 2147483648u32 and b == 0u32) implies not result;
} by {
    if a == 2147483648u32 and b == 0u32 { step_until(function.exit); solve(); }
    else { step_until(function.exit); solve(); }
}

bool sign_bit_set(uint32 u) {
    ensures result implies u > 2147483647u32;
    ensures u > 2147483647u32 implies result;
}
