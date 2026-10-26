theorem int32_increment_upper_bound(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value + 1) <= to_integer(upper);
}

theorem int32_increment_strictly_increases(value: int32, upper: int32) {
    requires value < upper;

    ensures to_integer(value) < to_integer(value + 1);
}

theorem int32_increment_lower_bound(value: int32, lower: int32, upper: int32) {
    requires lower <= value;
    requires value < upper;

    ensures to_integer(lower) <= to_integer(value + 1);
}

theorem int32_positive_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= value;
}

theorem int32_increment_below_max_is_defined(value: int32) {
    requires value < 2147483647;

    ensures defined(value + 1);
}

theorem int32_nonnegative_add_within_max_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires to_integer(value) <= to_integer(2147483647 - amount);

    ensures defined(value + amount);
}

theorem int32_nonnegative_subtract_within_value_is_defined(value: int32, amount: int32) {
    requires 0 <= amount;
    requires amount <= value;

    ensures defined(value - amount);
}

theorem int32_positive_predecessor_is_nonnegative(value: int32) {
    requires 0 < value;

    ensures 0 <= to_integer(value - 1);
}

theorem int32_positive_predecessor_strictly_decreases(value: int32) {
    requires 0 < value;

    ensures to_integer(value - 1) < to_integer(value);
}

theorem uint32_positive_predecessor_strictly_decreases(value: uint32) {
    requires 0u32 < value;

    ensures to_integer(value - 1u32) < to_integer(value);
}

theorem uint32_increment_upper_bound(value: uint32, upper: uint32) {
    requires value < upper;

    ensures to_integer(value + 1u32) <= to_integer(upper);
}

theorem uint32_less_than_implies_positive_difference(value: uint32, upper: uint32) {
    requires value < upper;

    ensures 0 < to_integer(upper - value);
}

theorem uint32_difference_decreases_after_increment(value: uint32, bound: uint32) {
    requires value < bound;

    ensures to_integer((0u32 - value) + (bound - 1u32)) < to_integer((0u32 - value) + bound);
}

theorem uint64_less_than_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first < middle;
    requires middle <= last;

    ensures first < last;
}

theorem uint64_less_equal_transitive(first: uint64, middle: uint64, last: uint64) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem int32_nonnegative_predecessor_upper_bound(value: int32, bound: int32) {
    requires 0 <= value;
    requires value <= bound;

    ensures to_integer(value - 1) <= to_integer(bound);
}

theorem int32_less_equal_less_than_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle < last;

    ensures first < last;
}

theorem int32_less_equal_transitive(first: int32, middle: int32, last: int32) {
    requires first <= middle;
    requires middle <= last;

    ensures first <= last;
}

theorem int32_less_equal_and_not_less_than_implies_equal(left: int32, right: int32) {
    requires left <= right;
    requires not (left < right);

    ensures left == right;
}

theorem int32_less_equal_and_not_equal_implies_less_than(left: int32, right: int32) {
    requires left <= right;
    requires left != right;

    ensures left < right;
}

// Wrapping unsigned arithmetic, the C operation itself. A specification that
// means C's modular result writes it with these, so it keeps that meaning
// where `+`, `-` and `*` compare exact Integers.
function uint32_wrapping_add(left: uint32, right: uint32) -> uint32 {
    left + right
}

function uint32_wrapping_sub(left: uint32, right: uint32) -> uint32 {
    left - right
}

function uint32_wrapping_mul(left: uint32, right: uint32) -> uint32 {
    left * right
}

function uint64_wrapping_add(left: uint64, right: uint64) -> uint64 {
    left + right
}

function uint64_wrapping_sub(left: uint64, right: uint64) -> uint64 {
    left - right
}

function uint64_wrapping_mul(left: uint64, right: uint64) -> uint64 {
    left * right
}

theorem uint32_add_to_integer(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

// Exact unsigned subtraction needs the native no-underflow guard.
theorem uint32_subtract_to_integer(left: uint32, right: uint32) {
    requires right <= left;
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem uint64_add_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) + to_integer(right) <= 18446744073709551615;
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem uint64_multiply_to_integer(left: uint64, right: uint64) {
    requires to_integer(left) * to_integer(right) <= 18446744073709551615;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}

theorem uint64_subtract_to_integer(left: uint64, right: uint64) {
    requires to_integer(right) <= to_integer(left);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem uint64_divide_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint64_remainder_to_integer(left: uint64, right: uint64) {
    requires right != 0u64;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint64_less_equal_to_integer(left: uint64, right: uint64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem uint64_to_integer_less_equal_implies_less_equal(left: uint64, right: uint64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem uint64_less_than_to_integer(left: uint64, right: uint64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}

theorem uint64_to_integer_less_than_implies_less_than(left: uint64, right: uint64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}

theorem uint32_pack_uint16_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

theorem uint32_pack_uint16_high_first_to_integer(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures to_integer((high << 16) | low) == to_integer(low) + 65536 * to_integer(high);
}

// Exact round trips of two bounded fields packed with the high field first.
theorem uint32_unpack_uint16_low(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures (((high << 16) | low) & 65535u32) == low;
}

theorem uint32_unpack_uint16_high(low: uint32, high: uint32) {
    requires low <= 65535u32;
    requires high <= 65535u32;
    ensures ((((high << 16) | low) >> 16) & 65535u32) == high;
}

theorem uint64_pack_uint16_to_integer(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures to_integer(low | (high << 16)) == to_integer(low) + 65536 * to_integer(high);
}

// LP64 C saves the same bounded fields in a uint64 result.
theorem uint64_unpack_uint16_low(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures ((low | (high << 16)) & 65535u64) == low;
}

theorem uint64_unpack_uint16_high(low: uint64, high: uint64) {
    requires low <= 65535u64;
    requires high <= 65535u64;
    ensures (((low | (high << 16)) >> 16) & 65535u64) == high;
}

theorem uint64_less_than_implies_not_greater_equal(left: uint64, right: uint64) {
    requires left < right;
    ensures not (left >= right);
}

theorem uint64_to_integer_equal_implies_equal(left: uint64, right: uint64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

// Exact observations of unsigned division require both evaluation domains.
theorem uint32_divide_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left / right) == truncating_quotient(to_integer(left), to_integer(right));
}

theorem uint32_remainder_to_integer(left: uint32, right: uint32) {
    requires right != 0u32;
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem uint32_multiply_to_integer(left: uint32, right: uint32) {
    requires right == 0u32 or left <= 4294967295u32 / right;
    ensures to_integer(left * right) == to_integer(left) * to_integer(right);
}

theorem uint32_multiply_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) * to_integer(right) <= 4294967295;
    ensures right == 0u32 or left <= 4294967295u32 / right;
}

theorem uint32_less_equal_to_integer(left: uint32, right: uint32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem uint32_to_integer_less_equal_implies_less_equal(left: uint32, right: uint32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem uint32_to_integer_equal_implies_equal(left: uint32, right: uint32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem uint32_remainder_less_than_divisor(value: uint32, divisor: uint32) {
    requires divisor != 0u32;
    ensures value % divisor < divisor;
}

theorem uint32_less_than_divisor_implies_remainder_is_value(value: uint32, divisor: uint32) {
    requires value < divisor;
    ensures value % divisor == value;
}

theorem uint32_to_integer_bounds(value: uint32) {
    ensures 0 <= to_integer(value) by {
        have 0u32 <= value;
        apply(integer::uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; };
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(integer::uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; };
    }
}

theorem uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by {
        have 0u64 <= value;
        apply(integer::uint64_less_equal_to_integer(0u64, value)) using { 0u64 <= value; };
    }
    ensures to_integer(value) <= 18446744073709551615 by {
        have value <= 18446744073709551615u64;
        apply(integer::uint64_less_equal_to_integer(value, 18446744073709551615u64)) using { value <= 18446744073709551615u64; };
    }
}

theorem int32_add_to_integer(left: int32, right: int32) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem int32_less_equal_to_integer(left: int32, right: int32) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem int64_less_equal_to_integer(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem int64_less_than_to_integer(left: int64, right: int64) {
    requires left < right;
    ensures to_integer(left) < to_integer(right);
}

theorem int64_greater_equal_to_integer(left: int64, right: int64) {
    requires left >= right;
    ensures to_integer(left) >= to_integer(right);
}

theorem int64_to_integer_less_equal_implies_less_equal(left: int64, right: int64) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem int64_to_integer_equal_implies_equal(left: int64, right: int64) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem int32_subtract_to_integer(left: int32, right: int32) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem int32_remainder_to_integer(left: int32, right: int32) {
    requires defined(left % right);
    requires to_integer(right) != 0;
    ensures to_integer(left % right) == truncating_remainder(to_integer(left), to_integer(right));
}

theorem int32_add_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) + to_integer(right) >= -2147483648;
    requires to_integer(left) + to_integer(right) <= 2147483647;
    ensures defined(left + right);
}

theorem to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}

theorem to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z;
}

theorem to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z;
}

theorem to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z;
}

theorem to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z;
}

theorem to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z;
}

theorem to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z;
}

theorem to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z;
}

theorem int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right);
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}

theorem floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; 0 <= r; };
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { solve() using { value == q + -1; }; }
            rewrite(value + 1 == q);
            solve() using { n == q * d + r; r < 0; };
        } else {
            have 0 <= r by { solve() using { not (r < 0); }; }
            have value == q;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        }
    }
}

theorem ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer::multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            solve() using { n == q * d + r; r <= d - 1; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            rewrite(value == q);
            solve() using { n == q * d + r; r <= 0; };
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { solve() using { value == q + 1; }; }
            rewrite(value + -1 == q);
            solve() using { n == q * d + r; 0 < r; };
        } else {
            have r <= 0 by { solve() using { not (0 < r); }; }
            have value == q;
            apply(integer::multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            solve() using { n == q * d + r; 1 - d <= r; };
        }
    }
}

theorem positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound * d <= n;
    ensures bound <= truncating_quotient(n, d) by {
        arithmetic_certificate rules {
            premise 0: bound * d <= n => bound * d <= n;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => bound <= truncating_quotient(n, d);
            conclusion 0;
        }
    }
}

theorem positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires n <= bound * d;
    ensures truncating_quotient(n, d) <= bound by {
        arithmetic_certificate rules {
            premise 0: n <= bound * d => n <= bound * d;
            premise 1: 1 <= d => 1 <= d;
            integer_quotient_bound bounds [0, 1] => truncating_quotient(n, d) <= bound;
            conclusion 0;
        }
    }
}

theorem positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { solve() using { bound * d < n; }; }
        apply(integer::positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            }; }
            if n <= 0 {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonpositive_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                }; }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { solve() using { not (n <= 0); }; }
                have 0 * d <= n by { solve() using { 0 <= n; }; }
                apply(integer::positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { solve() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                }; }
                contradiction(bound < 0);
            }
        }
    }
}

theorem positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { solve() using { n < bound * d; }; }
        apply(integer::positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { solve() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            }; }
            if 0 <= n {
                have 0 < d by { solve() using { 1 <= d; }; }
                apply(integer::nonnegative_dividend_remainder(n, d));
                apply(integer::truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { solve() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                }; }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { solve() using { not (0 <= n); }; }
                have n <= 0 * d by { solve() using { n <= 0; }; }
                apply(integer::positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { solve() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                }; }
                contradiction(0 < bound);
            }
        }
    }
}

theorem lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { solve() using { lower <= q; not (lower + 1 <= q); }; }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { solve() using { lower * d <= n; n == lower * d + r; }; }
            contradiction(r < 0);
        }
    }
}

theorem upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { solve() using { q <= upper; not (q <= upper + -1); }; }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { solve() using { n <= upper * d; n == upper * d + r; }; }
            contradiction(0 < r);
        }
    }
}
theorem multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires 0 <= factor;
    ensures a * factor <= b * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: 0 <= factor => 0 <= factor;
            integer_multiply_order bounds [0, 1] => a * factor <= b * factor;
            conclusion 0;
        }
    }
}

theorem multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
    requires a <= b;
    requires factor <= 0;
    ensures b * factor <= a * factor by {
        arithmetic_certificate rules {
            premise 0: a <= b => a <= b;
            premise 1: factor <= 0 => factor <= 0;
            integer_multiply_order bounds [0, 1] => b * factor <= a * factor;
            conclusion 0;
        }
    }
}

theorem scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer::multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        solve() using { lower * size <= lower * amount; lower * amount <= value * amount; };
    }
    ensures value * amount <= upper * size by {
        apply(integer::multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        solve() using { value * amount <= upper * amount; upper * amount <= upper * size; };
    }
}

// A native nonzero quotient guard bounds the exact Integer product.
theorem uint64_product_bound_from_division(x: uint64, y: uint64) {
    requires y != 0u64;
    requires x <= 18446744073709551615u64 / y;
    ensures to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64) by {
        have to_integer(y) != 0;
        have 0 <= to_integer(y);
        have 0 <= to_integer(18446744073709551615u64) by normalize();
        apply(integer::uint64_divide_to_integer(18446744073709551615u64, y)) using {
            y != 0u64;
            to_integer(y) != 0;
        };
        have to_integer(x) <= to_integer(18446744073709551615u64 / y);
        apply(integer::multiply_order_nonnegative(to_integer(x), to_integer(18446744073709551615u64 / y), to_integer(y))) using {
            to_integer(x) <= to_integer(18446744073709551615u64 / y);
            0 <= to_integer(y);
            y != 0u64;
        };
        apply(integer::truncation_identity(to_integer(18446744073709551615u64), to_integer(y))) using { to_integer(y) != 0; };
        apply(integer::nonnegative_dividend_remainder(to_integer(18446744073709551615u64), to_integer(y))) using {
            to_integer(y) != 0;
            0 <= to_integer(18446744073709551615u64);
        };
        have to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) by {
            rewrite(to_integer(18446744073709551615u64 / y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)));
            normalize();
        }
        solve() using {
            to_integer(x) * to_integer(y) <= to_integer(18446744073709551615u64 / y) * to_integer(y);
            to_integer(18446744073709551615u64 / y) * to_integer(y) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y);
            to_integer(18446744073709551615u64) == truncating_quotient(to_integer(18446744073709551615u64), to_integer(y)) * to_integer(y) + truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
            0 <= truncating_remainder(to_integer(18446744073709551615u64), to_integer(y));
        };
    }
}
