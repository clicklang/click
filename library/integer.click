theorem uint32_widened_add_guard_by_integer_bound(left: uint32, right: uint32) {
    requires to_integer(left) + to_integer(right) <= 4294967295;
    ensures ((int64)left + (int64)right) <= 4294967295i64;
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

theorem uint32_less_than_to_integer(left: uint32, right: uint32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(uint32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
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
        apply(uint32_less_equal_to_integer(0u32, value)) using { 0u32 <= value; }
    }
    ensures to_integer(value) <= 4294967295 by {
        have value <= 4294967295u32;
        apply(uint32_less_equal_to_integer(value, 4294967295u32)) using { value <= 4294967295u32; }
    }
}

// Checked source proof of the mathematical domain from native nonzero.
theorem uint32_nonzero_to_integer(value: uint32) {
 requires value != 0u32;
 ensures to_integer(value) != 0 by {
  apply(uint32_remainder_less_than_divisor(0u32, value)) using { value != 0u32; }
  apply(uint32_less_than_to_integer(0u32 % value, value)) using { 0u32 % value < value; }
  apply(uint32_to_integer_bounds(0u32 % value));
  have 1 <= to_integer(value) by {
   arithmetic() using { 0 <= to_integer(0u32 % value); to_integer(0u32 % value) < to_integer(value); }
  }
  arithmetic_certificate rules {
   premise 0: 1 <= to_integer(value) => 1 <= to_integer(value);
   integer_bound_exclusion bounds [0] => to_integer(value) != 0;
   conclusion 0;
  }
 }
}

theorem uint64_to_integer_bounds(value: uint64) {
    ensures 0 <= to_integer(value) by {
        have 0u64 <= value;
        apply(uint64_less_equal_to_integer(0u64, value)) using { 0u64 <= value; }
    }
    ensures to_integer(value) <= 18446744073709551615 by {
        have value <= 18446744073709551615u64;
        apply(uint64_less_equal_to_integer(value, 18446744073709551615u64)) using { value <= 18446744073709551615u64; }
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

theorem int32_to_integer_bounds(value: int32) {
    ensures -2147483648 <= to_integer(value) by {
        have -2147483648 <= value;
        apply(int32_less_equal_to_integer(-2147483648, value)) using { -2147483648 <= value; }
    }
    ensures to_integer(value) <= 2147483647 by {
        have value <= 2147483647;
        apply(int32_less_equal_to_integer(value, 2147483647)) using { value <= 2147483647; }
    }
}

theorem int32_to_integer_equal_implies_equal(left: int32, right: int32) {
    requires to_integer(left) == to_integer(right);
    ensures left == right;
}

theorem int32_to_integer_less_equal_implies_less_equal(left: int32, right: int32) {
    requires to_integer(left) <= to_integer(right);
    ensures left <= right;
}

theorem int32_less_than_to_integer(left: int32, right: int32) {
    requires left < right;
    ensures to_integer(left) < to_integer(right) by {
        if to_integer(right) <= to_integer(left) {
            apply(int32_to_integer_less_equal_implies_less_equal(right, left));
            contradiction(left < right);
        } else {
            arithmetic() using { not (to_integer(right) <= to_integer(left)); }
        }
    }
}

theorem int64_less_equal_to_integer(left: int64, right: int64) {
    requires left <= right;
    ensures to_integer(left) <= to_integer(right);
}

theorem int64_to_integer_bounds(value: int64) {
    ensures -9223372036854775808 <= to_integer(value) by {
        have -9223372036854775808i64 <= value;
        apply(int64_less_equal_to_integer(-9223372036854775808i64, value)) using { -9223372036854775808i64 <= value; }
    }
    ensures to_integer(value) <= 9223372036854775807 by {
        have value <= 9223372036854775807i64;
        apply(int64_less_equal_to_integer(value, 9223372036854775807i64)) using { value <= 9223372036854775807i64; }
    }
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

theorem int32_subtract_defined_by_integer_bounds(left: int32, right: int32) {
    requires to_integer(left) - to_integer(right) >= -2147483648;
    requires to_integer(left) - to_integer(right) <= 2147483647;
    ensures defined(left - right);
}

theorem integer_to_int8_round_trip(z: Integer) {
    requires z >= -128;
    requires z <= 127;
    ensures to_integer(to_int8(z)) == z;
}

theorem integer_to_int16_round_trip(z: Integer) {
    requires z >= -32768;
    requires z <= 32767;
    ensures to_integer(to_int16(z)) == z;
}

theorem integer_to_int32_round_trip(z: Integer) {
    requires z >= -2147483648;
    requires z <= 2147483647;
    ensures to_integer(to_int32(z)) == z;
}

theorem integer_to_uint8_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 255;
    ensures to_integer(to_uint8(z)) == z;
}

theorem integer_to_uint16_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 65535;
    ensures to_integer(to_uint16(z)) == z;
}

theorem integer_to_uint32_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 4294967295;
    ensures to_integer(to_uint32(z)) == z;
}

theorem integer_to_int64_round_trip(z: Integer) {
    requires z >= -9223372036854775808;
    requires z <= 9223372036854775807;
    ensures to_integer(to_int64(z)) == z;
}

theorem integer_to_uint64_round_trip(z: Integer) {
    requires z >= 0;
    requires z <= 18446744073709551615;
    ensures to_integer(to_uint64(z)) == z;
}

theorem int64_add_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) + to_integer(right) >= -9223372036854775808;
    requires to_integer(left) + to_integer(right) <= 9223372036854775807;
    ensures defined(left + right);
}

theorem int64_subtract_defined_by_integer_bounds(left: int64, right: int64) {
    requires to_integer(left) - to_integer(right) >= -9223372036854775808;
    requires to_integer(left) - to_integer(right) <= 9223372036854775807;
    ensures defined(left - right);
}

theorem int64_to_integer_less_than_implies_less_than(left: int64, right: int64) {
    requires to_integer(left) < to_integer(right);
    ensures left < right;
}

theorem int64_add_to_integer(left: int64, right: int64) {
    requires defined(left + right);
    ensures to_integer(left + right) == to_integer(left) + to_integer(right);
}

theorem int64_subtract_to_integer(left: int64, right: int64) {
    requires defined(left - right);
    ensures to_integer(left - right) == to_integer(left) - to_integer(right);
}

theorem integer_truncation_identity(n: Integer, d: Integer) {
    requires d != 0;
    ensures n == truncating_quotient(n, d) * d + truncating_remainder(n, d);
}

theorem integer_positive_divisor_remainder_lower(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures 1 - d <= truncating_remainder(n, d);
}

theorem integer_positive_divisor_remainder_upper(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 < d;
    ensures truncating_remainder(n, d) <= d - 1;
}

theorem integer_nonnegative_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires 0 <= n;
    ensures 0 <= truncating_remainder(n, d);
}

theorem integer_nonpositive_dividend_remainder(n: Integer, d: Integer) {
    requires d != 0;
    requires n <= 0;
    ensures truncating_remainder(n, d) <= 0;
}


theorem integer_multiply_add(a: Integer, b: Integer, c: Integer) {
    ensures (a + b) * c == a * c + b * c by {
        arithmetic_certificate rules {
            integer_polynomial_identity bounds [] => (a + b) * c == a * c + b * c;
            conclusion 0;
        }
    }
}

theorem integer_floor_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires r < 0 implies value == q + -1;
    requires 0 <= r implies value == q;
    ensures value * d <= n by {
        if r < 0 {
            have value == q + -1;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q + -1);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; 0 <= r; }
        }
    }
    ensures n < (value + 1) * d by {
        if r < 0 {
            have value == q + -1;
            have value + 1 == q by { arithmetic() using { value == q + -1; } }
            rewrite(value + 1 == q);
            arithmetic() using { n == q * d + r; r < 0; }
        } else {
            have 0 <= r by { arithmetic() using { not (r < 0); } }
            have value == q;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        }
    }
}

theorem integer_ceiling_from_remainder(n: Integer, d: Integer, q: Integer, r: Integer, value: Integer) {
    requires 0 < d;
    requires n == q * d + r;
    requires 1 - d <= r;
    requires r <= d - 1;
    requires 0 < r implies value == q + 1;
    requires r <= 0 implies value == q;
    ensures n <= value * d by {
        if 0 < r {
            have value == q + 1;
            apply(integer_multiply_add(q, 1, d));
            rewrite(value == q + 1);
            rewrite((q + 1) * d == q * d + 1 * d);
            arithmetic() using { n == q * d + r; r <= d - 1; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            rewrite(value == q);
            arithmetic() using { n == q * d + r; r <= 0; }
        }
    }
    ensures (value + -1) * d < n by {
        if 0 < r {
            have value == q + 1;
            have value + -1 == q by { arithmetic() using { value == q + 1; } }
            rewrite(value + -1 == q);
            arithmetic() using { n == q * d + r; 0 < r; }
        } else {
            have r <= 0 by { arithmetic() using { not (0 < r); } }
            have value == q;
            apply(integer_multiply_add(q, -1, d));
            rewrite(value == q);
            rewrite((q + -1) * d == q * d + -1 * d);
            arithmetic() using { n == q * d + r; 1 - d <= r; }
        }
    }
}

theorem integer_positive_divisor_quotient_lower(n: Integer, d: Integer, bound: Integer) {
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

theorem integer_positive_divisor_quotient_upper(n: Integer, d: Integer, bound: Integer) {
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

theorem integer_positive_divisor_quotient_strict_lower(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires bound < 0;
    requires bound * d < n;
    ensures bound < truncating_quotient(n, d) by {
        have bound * d <= n by { arithmetic() using { bound * d < n; } }
        apply(integer_positive_divisor_quotient_lower(n, d, bound));
        if bound < truncating_quotient(n, d) {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                bound <= truncating_quotient(n, d); not (bound < truncating_quotient(n, d));
            } }
            if n <= 0 {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonpositive_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (bound * d < n) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); truncating_remainder(n, d) <= 0;
                } }
                contradiction(bound * d < n);
            } else {
                have 0 <= n by { arithmetic() using { not (n <= 0); } }
                have 0 * d <= n by { arithmetic() using { 0 <= n; } }
                apply(integer_positive_divisor_quotient_lower(n, d, 0));
                have not (bound < 0) by { arithmetic() using {
                    0 <= truncating_quotient(n, d); truncating_quotient(n, d) == bound;
                } }
                contradiction(bound < 0);
            }
        }
    }
}

theorem integer_positive_divisor_quotient_strict_upper(n: Integer, d: Integer, bound: Integer) {
    requires d != 0;
    requires 1 <= d;
    requires 0 < bound;
    requires n < bound * d;
    ensures truncating_quotient(n, d) < bound by {
        have n <= bound * d by { arithmetic() using { n < bound * d; } }
        apply(integer_positive_divisor_quotient_upper(n, d, bound));
        if truncating_quotient(n, d) < bound {
            assumption();
        } else {
            have truncating_quotient(n, d) == bound by { arithmetic() using {
                truncating_quotient(n, d) <= bound; not (truncating_quotient(n, d) < bound);
            } }
            if 0 <= n {
                have 0 < d by { arithmetic() using { 1 <= d; } }
                apply(integer_nonnegative_dividend_remainder(n, d));
                apply(integer_truncation_identity(n, d));
                have n == bound * d + truncating_remainder(n, d) by {
                    rewrite(bound == truncating_quotient(n, d));
                    assumption();
                }
                have not (n < bound * d) by { arithmetic() using {
                    n == bound * d + truncating_remainder(n, d); 0 <= truncating_remainder(n, d);
                } }
                contradiction(n < bound * d);
            } else {
                have n <= 0 by { arithmetic() using { not (0 <= n); } }
                have n <= 0 * d by { arithmetic() using { n <= 0; } }
                apply(integer_positive_divisor_quotient_upper(n, d, 0));
                have not (0 < bound) by { arithmetic() using {
                    truncating_quotient(n, d) <= 0; truncating_quotient(n, d) == bound;
                } }
                contradiction(0 < bound);
            }
        }
    }
}

theorem integer_lower_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, lower: Integer) {
    requires lower <= q;
    requires lower * d <= n;
    requires n == q * d + r;
    requires r < 0;
    ensures lower + 1 <= q by {
        if lower + 1 <= q {
            assumption();
        } else {
            have q == lower by { arithmetic() using { lower <= q; not (lower + 1 <= q); } }
            have n == lower * d + r by {
                rewrite(lower == q);
                assumption();
            }
            have not (r < 0) by { arithmetic() using { lower * d <= n; n == lower * d + r; } }
            contradiction(r < 0);
        }
    }
}

theorem integer_upper_correction_bound(n: Integer, d: Integer, q: Integer, r: Integer, upper: Integer) {
    requires q <= upper;
    requires n <= upper * d;
    requires n == q * d + r;
    requires 0 < r;
    ensures q <= upper + -1 by {
        if q <= upper + -1 {
            assumption();
        } else {
            have q == upper by { arithmetic() using { q <= upper; not (q <= upper + -1); } }
            have n == upper * d + r by {
                rewrite(upper == q);
                assumption();
            }
            have not (0 < r) by { arithmetic() using { n <= upper * d; n == upper * d + r; } }
            contradiction(0 < r);
        }
    }
}
theorem integer_multiply_order_nonnegative(a: Integer, b: Integer, factor: Integer) {
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

theorem integer_multiply_order_nonpositive(a: Integer, b: Integer, factor: Integer) {
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

theorem integer_scaled_product_bounds(value: Integer, amount: Integer, size: Integer, lower: Integer, upper: Integer) {
    requires lower <= value;
    requires value <= upper;
    requires lower <= 0;
    requires 0 <= upper;
    requires 0 <= amount;
    requires amount <= size;
    ensures lower * size <= value * amount by {
        apply(integer_multiply_order_nonnegative(lower, value, amount));
        have lower * size <= lower * amount by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: lower <= 0 => lower <= 0;
                integer_multiply_order bounds [0, 1] => lower * size <= lower * amount;
                conclusion 0;
            }
        }
        arithmetic() using { lower * size <= lower * amount; lower * amount <= value * amount; }
    }
    ensures value * amount <= upper * size by {
        apply(integer_multiply_order_nonnegative(value, upper, amount));
        have upper * amount <= upper * size by {
            arithmetic_certificate rules {
                premise 0: amount <= size => amount <= size;
                premise 1: 0 <= upper => 0 <= upper;
                integer_multiply_order bounds [0, 1] => upper * amount <= upper * size;
                conclusion 0;
            }
        }
        arithmetic() using { value * amount <= upper * amount; upper * amount <= upper * size; }
    }
}
