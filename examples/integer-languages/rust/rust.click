// The Rust side of the cross-language integer fixture
// (`tests/examples/integer_languages.rs`): the same claims as `../c/c.click`
// and `../cpp/cpp.click`. A case Rust does not verify yet is in `rust.click-
// gap`.

import click::integer;

verifying "integers.rs";

fn add_i32(a: i32, b: i32) -> i32 {
    requires -2147483648 <= a + b and a + b <= 2147483647;
    ensures result == a + b;
} by { execute(); solve(); }

fn sub_i32(a: i32, b: i32) -> i32 {
    requires -2147483648 <= a - b and a - b <= 2147483647;
    ensures result == a - b;
} by { execute(); solve(); }

fn mul_i32(a: i32, b: i32) -> i32 {
    requires -2147483648 <= a * b and a * b <= 2147483647;
    ensures result == a * b;
} by {
    execute();
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

fn above_int32_max() -> u32 {
    ensures result == 4000000000u32;
    ensures result > 2147483647u32;
} by { execute(); solve(); }

fn keep_above_int32_max(u: u32) -> u32 {
    ensures u > 2147483647u32 implies result == u;
    ensures u <= 2147483647u32 implies result == 0u32;
    ensures u == 4000000000u32 implies result == 4000000000u32;
} by { execute(); solve(); }

fn to_signed_i32(u: u32) -> i32 {
    ensures result == (int32) u;
    ensures u == 4294967295u32 implies result == -1;
    ensures u == 2147483648u32 implies result == -2147483648;
} by { execute(); solve(); }

fn to_unsigned_u32(x: i32) -> u32 {
    ensures result == (uint32) x;
    ensures x == -1 implies result == 4294967295u32;
    ensures (int32) result == x;
} by { execute(); solve(); }

fn div_u32(a: u32, b: u32) -> u32 {
    requires b != 0u32;
    ensures result == a / b;
    ensures (a == 4294967295u32 and b == 2u32) implies result == 2147483647u32;
} by { execute(); solve(); }

fn rem_u32(a: u32, b: u32) -> u32 {
    requires b != 0u32;
    ensures result == a % b;
    ensures (a == 4294967295u32 and b == 10u32) implies result == 5u32;
} by { execute(); solve(); }

fn shr_u32(a: u32, n: u32) -> u32 {
    requires n < 32u32;
    ensures result == a >> n;
    ensures (a == 2147483648u32 and n == 1u32) implies result == 1073741824u32;
} by { execute(); solve(); }

fn div_i32(a: i32, b: i32) -> i32 {
    requires b != 0;
    requires a != -2147483648 or b != -1;
    ensures result == a / b;
    ensures (a == -7 and b == 2) implies result == -3;
    ensures (a == 7 and b == -2) implies result == -3;
} by { execute(); solve(); }

fn rem_i32(a: i32, b: i32) -> i32 {
    requires b != 0;
    requires a != -2147483648 or b != -1;
    ensures result == a % b;
    ensures (a == -7 and b == 2) implies result == -1;
    ensures (a == 7 and b == -2) implies result == 1;
} by { execute(); solve(); }

fn shr_i32(a: i32, n: u32) -> i32 {
    requires n < 32u32;
    ensures result == a >> n;
    ensures (a == -8 and n == 1u32) implies result == -4;
} by { execute(); solve(); }

fn narrow_u8(x: u32) -> u8 {
    ensures (uint32) result == (x & 255u32);
    ensures x == 4000000000u32 implies result == 0u8;
    ensures x == 300u32 implies result == 44u8;
} by { execute(); solve(); }

fn narrow_u8_in_range(x: u32) -> u8 {
    requires x <= 255u32;
    ensures to_integer(result) == to_integer(x);
} by {
    execute();
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

fn add_i64(a: i64, b: i64) -> i64 {
    requires -9223372036854775808 <= a + b and a + b <= 9223372036854775807;
    ensures result == a + b;
} by { execute(); solve(); }

fn below_i32(a: i32, b: i32) -> bool {
    ensures result implies a < b;
    ensures a < b implies result;
    ensures (a == -2147483648 and b == 0) implies result;
} by {
    if a == -2147483648 and b == 0 { execute(); solve(); }
    else { execute(); solve(); }
}

fn below_u32(a: u32, b: u32) -> bool {
    ensures result implies a < b;
    ensures a < b implies result;
    ensures (a == 2147483648u32 and b == 0u32) implies not result;
} by {
    if a == 2147483648u32 and b == 0u32 { execute(); solve(); }
    else { execute(); solve(); }
}

fn sign_bit_set(u: u32) -> bool {
    ensures result implies u > 2147483647u32;
    ensures u > 2147483647u32 implies result;
} by { execute(); solve(); }
