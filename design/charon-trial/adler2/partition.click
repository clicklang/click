theorem adler_small_quotient_bounds(n: Integer, d: Integer) {
 requires 0 <= n;
 requires n <= 22207;
 requires 4 <= d;
 requires d != 0;
 ensures 0 <= truncating_quotient(n, d) by {
  have 1 <= d by { arithmetic() using { 4 <= d; } }
  have 0 * d <= n by { arithmetic() using { 0 <= n; } }
  apply(integer_positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; }
 }
 ensures truncating_quotient(n, d) <= 5551 by {
  have 1 <= d by { arithmetic() using { 4 <= d; } }
  have n < 5552 * d by { arithmetic() using { n <= 22207; 4 <= d; } }
  apply(integer_positive_divisor_quotient_strict_upper(n, d, 5552)) using { d != 0; 1 <= d; n < 5552 * d; }
  arithmetic() using { truncating_quotient(n, d) < 5552; }
 }
}
function adler_vector_prefix(n: Integer) -> Integer {
 n - truncating_remainder(n, 4)
}
theorem adler_small_partition(n: Integer) {
 requires 0 <= n;
 requires n <= 22207;
 ensures 0 <= adler_vector_prefix(n) and adler_vector_prefix(n) <= 22204 by {
  apply(integer_truncation_identity(n, 4)) using { 4 != 0; }
  apply(adler_small_quotient_bounds(n, 4)) using { 0 <= n; n <= 22207; 4 <= 4; 4 != 0; }
  unfold(adler_vector_prefix(n));
  both {
   arithmetic() using { n == truncating_quotient(n, 4) * 4 + truncating_remainder(n, 4); 0 <= truncating_quotient(n, 4); }
  } and {
   arithmetic() using { n == truncating_quotient(n, 4) * 4 + truncating_remainder(n, 4); truncating_quotient(n, 4) <= 5551; }
  }
 }
 ensures 0 <= truncating_remainder(n, 4) by {
  apply(integer_nonnegative_dividend_remainder(n, 4)) using { 4 != 0; 0 <= n; }
 }
 ensures truncating_remainder(n, 4) <= 3 by {
  apply(integer_positive_divisor_remainder_upper(n, 4)) using { 4 != 0; 0 < 4; }
 }
}

theorem adler_unsigned_small_partition(n: uint64) {
 requires n <= 22207u64;
 ensures 0 <= to_integer(n - n % 4u64) and to_integer(n - n % 4u64) <= 22204 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22207u64)) using { n <= 22207u64; }
  apply(adler_small_partition(to_integer(n))) using { 0 <= to_integer(n); to_integer(n) <= 22207; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer(n % 4u64) <= to_integer(n) by {
   rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
   have 0 <= to_integer(n) - truncating_remainder(to_integer(n), 4) by {
    unfold(adler_vector_prefix(to_integer(n)));
    arithmetic() using { 0 <= adler_vector_prefix(to_integer(n)); adler_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
   }
   arithmetic() using { 0 <= to_integer(n) - truncating_remainder(to_integer(n), 4); }
  }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  rewrite(to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64));
  rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
  unfold(adler_vector_prefix(to_integer(n)));
  both {
   arithmetic() using { 0 <= adler_vector_prefix(to_integer(n)); adler_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
  } and {
   arithmetic() using { adler_vector_prefix(to_integer(n)) <= 22204; adler_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
  }
 }
}

theorem adler_signed_small_prefix(n: uint64) {
 requires n <= 22207u64;
 ensures 0 <= (int32)(uint32)(n - n % 4u64) and (int32)(uint32)(n - n % 4u64) <= 22204 by {
  apply(adler_unsigned_small_partition(n)) using { n <= 22207u64; }
  have n % 4u64 <= n by { normalize(); }
  have n - n % 4u64 <= n by { normalize() using { n % 4u64 <= n; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= n; n <= 22207u64; } }
  have to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n - n % 4u64) => 0 <= to_integer(n - n % 4u64);
    premise 1: to_integer(n - n % 4u64) <= 22204 => to_integer(n - n % 4u64) <= 22204;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)(n - n % 4u64)) by { rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64)); assumption(); }
  have to_integer((int32)(uint32)(n - n % 4u64)) <= 22204 by { rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64)); assumption(); }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)(n - n % 4u64))) using { 0 <= to_integer((int32)(uint32)(n - n % 4u64)); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)(n - n % 4u64), 22204)) using { to_integer((int32)(uint32)(n - n % 4u64)) <= 22204; }
  }
 }
}

theorem adler_multiple_of_four(n: Integer) {
 requires 0 <= n;
 ensures truncating_remainder(n * 4, 4) == 0 by {
  apply(integer_positive_divisor_quotient_lower(n * 4, 4, n)) using { 4 != 0; 1 <= 4; n * 4 <= n * 4; }
  have 0 < n + 1 by { arithmetic() using { 0 <= n; } }
  have n * 4 < (n + 1) * 4 by { arithmetic() using {}; }
  apply(integer_positive_divisor_quotient_strict_upper(n * 4, 4, n + 1)) using { 4 != 0; 1 <= 4; 0 < n + 1; n * 4 < (n + 1) * 4; }
  have truncating_quotient(n * 4, 4) == n by { arithmetic() using { n <= truncating_quotient(n * 4, 4); truncating_quotient(n * 4, 4) < n + 1; } }
  apply(integer_truncation_identity(n * 4, 4)) using { 4 != 0; }
  arithmetic() using { n * 4 == truncating_quotient(n * 4, 4) * 4 + truncating_remainder(n * 4, 4); truncating_quotient(n * 4, 4) == n; }
 }
}

theorem adler_int32_multiple_of_four(n: int32, q: Integer) {
 requires 0 <= q;
 requires to_integer(n) == q * 4;
 ensures n % 4 == 0 by {
  have defined(n % 4) by { normalize(); }
  apply(int32_remainder_to_integer(n, 4)) using { defined(n % 4); to_integer(4) != 0; }
  apply(adler_multiple_of_four(q)) using { 0 <= q; }
  have to_integer(n % 4) == 0 by {
   rewrite(to_integer(n % 4) == truncating_remainder(to_integer(n), to_integer(4)));
   rewrite(to_integer(n) == q * 4);
   assumption();
  }
  apply(int32_equal_of_to_integer(n % 4, 0)) using { to_integer(n % 4) == 0; }
 }
}

theorem adler_small_prefix_divisible(n: uint64) {
 requires n <= 22207u64;
 ensures (int32)(uint32)(n - n % 4u64) % 4 == 0 by {
  apply(adler_unsigned_small_partition(n)) using { n <= 22207u64; }
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22207u64)) using { n <= 22207u64; }
  apply(adler_small_quotient_bounds(to_integer(n), 4)) using { 0 <= to_integer(n); to_integer(n) <= 22207; 4 <= 4; 4 != 0; }
  apply(integer_truncation_identity(to_integer(n), 4)) using { 4 != 0; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have to_integer(n - n % 4u64) == truncating_quotient(to_integer(n), 4) * 4 by {
   rewrite(to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64));
   rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
   arithmetic() using { to_integer(n) == truncating_quotient(to_integer(n), 4) * 4 + truncating_remainder(to_integer(n), 4); }
  }
  have n - n % 4u64 <= n by { normalize() using { n % 4u64 <= n; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= n; n <= 22207u64; } }
  have to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n - n % 4u64) => 0 <= to_integer(n - n % 4u64);
    premise 1: to_integer(n - n % 4u64) <= 22204 => to_integer(n - n % 4u64) <= 22204;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64);
    conclusion 0;
   }
  }
  have to_integer((int32)(uint32)(n - n % 4u64)) == truncating_quotient(to_integer(n), 4) * 4 by {
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   assumption();
  }
  apply(adler_int32_multiple_of_four((int32)(uint32)(n - n % 4u64), truncating_quotient(to_integer(n), 4))) using { 0 <= truncating_quotient(to_integer(n), 4); to_integer((int32)(uint32)(n - n % 4u64)) == truncating_quotient(to_integer(n), 4) * 4; }
 }
}

theorem adler_uint64_bounded_equality(left: uint64, right: uint64) {
 requires to_integer(left) == to_integer(right);
 requires 0 <= to_integer(left);
 requires to_integer(left) <= 2147483647;
 requires 0 <= to_integer(right);
 requires to_integer(right) <= 2147483647;
 ensures left == right by {
  have to_integer(left) <= to_integer(9223372036854775807u64) by { arithmetic() using { to_integer(left) <= 2147483647; } }
  have left <= 9223372036854775807u64 by { apply(uint64_less_equal_of_to_integer(left, 9223372036854775807u64)) using { to_integer(left) <= to_integer(9223372036854775807u64); } }
  have to_integer(right) <= to_integer(9223372036854775807u64) by { arithmetic() using { to_integer(right) <= 2147483647; } }
  have right <= 9223372036854775807u64 by { apply(uint64_less_equal_of_to_integer(right, 9223372036854775807u64)) using { to_integer(right) <= to_integer(9223372036854775807u64); } }
  have to_integer((int64)left) == to_integer(left) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(left) => 0 <= to_integer(left);
    premise 1: to_integer(left) <= 2147483647 => to_integer(left) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int64)left) == to_integer(left);
    conclusion 0;
   }
  }
  have to_integer((int64)right) == to_integer(right) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(right) => 0 <= to_integer(right);
    premise 1: to_integer(right) <= 2147483647 => to_integer(right) <= 2147483647;
    integer_cast_identity bounds [0, 1] => to_integer((int64)right) == to_integer(right);
    conclusion 0;
   }
  }
  have to_integer((int64)left) == to_integer((int64)right) by {
   rewrite(to_integer((int64)left) == to_integer(left));
   rewrite(to_integer((int64)right) == to_integer(right));
   assumption();
  }
  have (int64)left == (int64)right by { apply(int64_equal_of_to_integer((int64)left, (int64)right)) using { to_integer((int64)left) == to_integer((int64)right); } }
  simp() using { (int64)left == (int64)right; }
 }
}

theorem adler_small_tail_metadata(n: uint64) {
 requires n <= 22207u64;
 ensures n - (n - n % 4u64) == n % 4u64 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22207u64)) using { n <= 22207u64; }
  apply(adler_small_partition(to_integer(n))) using { 0 <= to_integer(n); to_integer(n) <= 22207; }
  have n % 4u64 <= n by { normalize(); }
  have n - n % 4u64 <= n by { normalize() using { n % 4u64 <= n; } }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_less_equal_to_integer(n - n % 4u64, n)) using { n - n % 4u64 <= n; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  apply(uint64_subtract_to_integer(n, n - n % 4u64)) using { to_integer(n - n % 4u64) <= to_integer(n); }
  have to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64) by {
   arithmetic() using { to_integer(n - (n - n % 4u64)) == to_integer(n) - to_integer(n - n % 4u64); to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64); }
  }
  have 0 <= to_integer(n % 4u64) by { rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64))); assumption(); }
  have to_integer(n % 4u64) <= 2147483647 by { rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64))); arithmetic() using { truncating_remainder(to_integer(n), 4) <= 3; } }
  have 0 <= to_integer(n - (n - n % 4u64)) by { rewrite(to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64)); assumption(); }
  have to_integer(n - (n - n % 4u64)) <= 2147483647 by { rewrite(to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64)); assumption(); }
  apply(adler_uint64_bounded_equality(n - (n - n % 4u64), n % 4u64)) using { to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64); 0 <= to_integer(n - (n - n % 4u64)); to_integer(n - (n - n % 4u64)) <= 2147483647; 0 <= to_integer(n % 4u64); to_integer(n % 4u64) <= 2147483647; }
 }
 ensures n % 4u64 <= 3u64 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  apply(integer_positive_divisor_remainder_upper(to_integer(n), 4)) using { 4 != 0; 0 < 4; }
  have to_integer(n % 4u64) <= to_integer(3u64) by { rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64))); assumption(); }
  apply(uint64_less_equal_of_to_integer(n % 4u64, 3u64)) using { to_integer(n % 4u64) <= to_integer(3u64); }
 }
}

theorem adler_small_native_prefix(n: uint64) {
 requires n <= 22207u64;
 ensures n - n % 4u64 <= 22204u64 by {
  apply(adler_unsigned_small_partition(n)) using { n <= 22207u64; }
  apply(uint64_less_equal_of_to_integer(n - n % 4u64, 22204u64)) using { to_integer(n - n % 4u64) <= 22204; }
 }
}
theorem adler_index_observation(n: uint64) {
 requires n <= 2147483647u64;
 ensures to_integer((int32)(uint32)n) == to_integer(n) by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  arithmetic_certificate special {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 2147483647 => to_integer(n) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)n) == to_integer(n);
   conclusion 0;
  }
 }
}
theorem adler_small_signed_tail(n: uint64) {
 requires n <= 22207u64;
 ensures 0 <= (int32)(uint32)(n % 4u64) and (int32)(uint32)(n % 4u64) <= 3 by {
  apply(adler_small_tail_metadata(n)) using { n <= 22207u64; }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have 0u64 <= n % 4u64 by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n % 4u64)) using { 0u64 <= n % 4u64; }
  apply(uint64_less_equal_to_integer(n % 4u64, 3u64)) using { n % 4u64 <= 3u64; }
  have 0 <= to_integer((int32)(uint32)(n % 4u64)) by { rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64)); assumption(); }
  have to_integer((int32)(uint32)(n % 4u64)) <= 3 by { rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64)); assumption(); }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)(n % 4u64))) using { 0 <= to_integer((int32)(uint32)(n % 4u64)); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)(n % 4u64), 3)) using { to_integer((int32)(uint32)(n % 4u64)) <= 3; }
  }
 }
}

theorem adler_signed_partition_identity(n: uint64) {
 requires n <= 22207u64;
 ensures (int32)(uint32)n == (int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64) by {
  apply(adler_signed_small_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_signed_tail(n)) using { n <= 22207u64; }
  apply(adler_small_native_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_tail_metadata(n)) using { n <= 22207u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 22204u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)) by { simp() using { 0 <= (int32)(uint32)(n - n % 4u64); (int32)(uint32)(n - n % 4u64) <= 22204; 0 <= (int32)(uint32)(n % 4u64); (int32)(uint32)(n % 4u64) <= 3; } }
  apply(int32_add_to_integer((int32)(uint32)(n - n % 4u64), (int32)(uint32)(n % 4u64))) using { defined((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)); }
  have to_integer((int32)(uint32)n) == to_integer((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)) by {
   rewrite(to_integer((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)) == to_integer((int32)(uint32)(n - n % 4u64)) + to_integer((int32)(uint32)(n % 4u64)));
   rewrite(to_integer((int32)(uint32)n) == to_integer(n));
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64));
   arithmetic() using { to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64); }
  }
  apply(int32_equal_of_to_integer((int32)(uint32)n, (int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64))) using { to_integer((int32)(uint32)n) == to_integer((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)); }
 }
}

theorem adler_short_integer_remainder(n: Integer, d: Integer) {
 requires 0 <= n;
 requires n < d;
 requires 1 <= d;
 requires d != 0;
 ensures truncating_remainder(n, d) == n by {
  have 0 * d <= n by { arithmetic() using { 0 <= n; } }
  have n < 1 * d by { arithmetic() using { n < d; } }
  apply(integer_positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; }
  apply(integer_positive_divisor_quotient_strict_upper(n, d, 1)) using { d != 0; 1 <= d; n < 1 * d; }
  have truncating_quotient(n, d) == 0 by { arithmetic() using { 0 <= truncating_quotient(n, d); truncating_quotient(n, d) < 1; } }
  apply(integer_truncation_identity(n, d)) using { d != 0; }
  have truncating_quotient(n, d) * d == 0 by { rewrite(truncating_quotient(n, d) == 0); normalize(); }
  arithmetic() using { n == truncating_quotient(n, d) * d + truncating_remainder(n, d); truncating_quotient(n, d) * d == 0; }
 }
}
theorem adler_small_outer_remainder(n: uint64) {
 requires n <= 22204u64;
 ensures n % 22208u64 == n by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22204u64)) using { n <= 22204u64; }
  have to_integer(n) < 22208 by { arithmetic() using { to_integer(n) <= 22204; } }
  apply(adler_short_integer_remainder(to_integer(n), 22208)) using { 0 <= to_integer(n); to_integer(n) < 22208; 1 <= 22208; 22208 != 0; }
  apply(uint64_remainder_to_integer(n, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; }
  have to_integer(n % 22208u64) == to_integer(n) by { rewrite(to_integer(n % 22208u64) == truncating_remainder(to_integer(n), to_integer(22208u64))); assumption(); }
  have 0 <= to_integer(n % 22208u64) by { rewrite(to_integer(n % 22208u64) == to_integer(n)); assumption(); }
  have to_integer(n % 22208u64) <= 2147483647 by { rewrite(to_integer(n % 22208u64) == to_integer(n)); arithmetic() using { to_integer(n) <= 22204; } }
  have to_integer(n) <= 2147483647 by { arithmetic() using { to_integer(n) <= 22204; } }
  apply(adler_uint64_bounded_equality(n % 22208u64, n)) using { to_integer(n % 22208u64) == to_integer(n); 0 <= to_integer(n % 22208u64); to_integer(n % 22208u64) <= 2147483647; 0 <= to_integer(n); to_integer(n) <= 2147483647; }
 }
}

theorem adler_native_small_prefix_divisible(n: uint64) {
 requires n <= 22207u64;
 ensures (n - n % 4u64) % 4u64 == 0u64 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22207u64)) using { n <= 22207u64; }
  apply(adler_small_quotient_bounds(to_integer(n), 4)) using { 0 <= to_integer(n); to_integer(n) <= 22207; 4 <= 4; 4 != 0; }
  apply(adler_multiple_of_four(truncating_quotient(to_integer(n), 4))) using { 0 <= truncating_quotient(to_integer(n), 4); }
  apply(integer_truncation_identity(to_integer(n), 4)) using { 4 != 0; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have to_integer(n - n % 4u64) == truncating_quotient(to_integer(n), 4) * 4 by {
   rewrite(to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64));
   rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
   arithmetic() using { to_integer(n) == truncating_quotient(to_integer(n), 4) * 4 + truncating_remainder(to_integer(n), 4); }
  }
  apply(uint64_remainder_to_integer(n - n % 4u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer((n - n % 4u64) % 4u64) == 0 by {
   rewrite(to_integer((n - n % 4u64) % 4u64) == truncating_remainder(to_integer(n - n % 4u64), to_integer(4u64)));
   rewrite(to_integer(n - n % 4u64) == truncating_quotient(to_integer(n), 4) * 4);
   assumption();
  }
  have 0 <= to_integer((n - n % 4u64) % 4u64) by { arithmetic() using { to_integer((n - n % 4u64) % 4u64) == 0; } }
  have to_integer((n - n % 4u64) % 4u64) <= 2147483647 by { arithmetic() using { to_integer((n - n % 4u64) % 4u64) == 0; } }
  apply(adler_uint64_bounded_equality((n - n % 4u64) % 4u64, 0u64)) using { to_integer((n - n % 4u64) % 4u64) == 0; 0 <= to_integer((n - n % 4u64) % 4u64); to_integer((n - n % 4u64) % 4u64) <= 2147483647; }
 }
}

theorem adler_small_prefix_within_full(n: uint64) {
 requires n <= 22207u64;
 ensures 0 <= (int32)(uint32)n and (int32)(uint32)n <= 22207 by {
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 22207u64)) using { n <= 22207u64; }
  have 0 <= to_integer((int32)(uint32)n) by { rewrite(to_integer((int32)(uint32)n) == to_integer(n)); assumption(); }
  have to_integer((int32)(uint32)n) <= 22207 by { rewrite(to_integer((int32)(uint32)n) == to_integer(n)); simp() using { to_integer(n) <= to_integer(22207u64); } }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)n)) using { 0 <= to_integer((int32)(uint32)n); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)n, 22207)) using { to_integer((int32)(uint32)n) <= 22207; }
  }
 }
 ensures (int32)(uint32)(n - n % 4u64) <= (int32)(uint32)n by {
  apply(adler_small_native_prefix(n)) using { n <= 22207u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 22204u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  have n - n % 4u64 <= n by { normalize() using { n % 4u64 <= n; } }
  apply(uint64_less_equal_to_integer(n - n % 4u64, n)) using { n - n % 4u64 <= n; }
  have to_integer((int32)(uint32)(n - n % 4u64)) <= to_integer((int32)(uint32)n) by {
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   rewrite(to_integer((int32)(uint32)n) == to_integer(n));
   assumption();
  }
  apply(int32_less_equal_of_to_integer((int32)(uint32)(n - n % 4u64), (int32)(uint32)n)) using { to_integer((int32)(uint32)(n - n % 4u64)) <= to_integer((int32)(uint32)n); }
 }
}

theorem adler_small_tail_indices(n: uint64) {
 requires n <= 22207u64;
 ensures (int32)(uint32)(n % 4u64) <= (int32)(uint32)n by {
  apply(adler_small_prefix_within_full(n)) using { n <= 22207u64; }
  apply(adler_signed_small_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_signed_tail(n)) using { n <= 22207u64; }
  apply(adler_small_native_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_tail_metadata(n)) using { n <= 22207u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 22204u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have to_integer((int32)(uint32)(n % 4u64)) <= to_integer((int32)(uint32)n) by {
   rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64));
   rewrite(to_integer((int32)(uint32)n) == to_integer(n));
   assumption();
  }
  apply(int32_less_equal_of_to_integer((int32)(uint32)(n % 4u64), (int32)(uint32)n)) using { to_integer((int32)(uint32)(n % 4u64)) <= to_integer((int32)(uint32)n); }
 }
 ensures (int32)(uint32)n - (int32)(uint32)(n % 4u64) == (int32)(uint32)(n - n % 4u64) by {
  apply(adler_small_prefix_within_full(n)) using { n <= 22207u64; }
  apply(adler_signed_small_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_signed_tail(n)) using { n <= 22207u64; }
  apply(adler_small_native_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_tail_metadata(n)) using { n <= 22207u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 22204u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)n - (int32)(uint32)(n % 4u64)) by { simp() using { 0 <= (int32)(uint32)n; (int32)(uint32)n <= 22207; 0 <= (int32)(uint32)(n % 4u64); (int32)(uint32)(n % 4u64) <= 3; } }
  apply(int32_subtract_to_integer((int32)(uint32)n, (int32)(uint32)(n % 4u64))) using { defined((int32)(uint32)n - (int32)(uint32)(n % 4u64)); }
  have to_integer((int32)(uint32)n - (int32)(uint32)(n % 4u64)) == to_integer((int32)(uint32)(n - n % 4u64)) by {
   rewrite(to_integer((int32)(uint32)n - (int32)(uint32)(n % 4u64)) == to_integer((int32)(uint32)n) - to_integer((int32)(uint32)(n % 4u64)));
   rewrite(to_integer((int32)(uint32)n) == to_integer(n));
   rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64));
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   arithmetic() using { to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64); }
  }
  apply(int32_equal_of_to_integer((int32)(uint32)n - (int32)(uint32)(n % 4u64), (int32)(uint32)(n - n % 4u64))) using { to_integer((int32)(uint32)n - (int32)(uint32)(n % 4u64)) == to_integer((int32)(uint32)(n - n % 4u64)); }
 }
 ensures (int32)(uint32)n - (int32)(uint32)(n - n % 4u64) == (int32)(uint32)(n % 4u64) by {
  apply(adler_small_prefix_within_full(n)) using { n <= 22207u64; }
  apply(adler_signed_small_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_signed_tail(n)) using { n <= 22207u64; }
  apply(adler_small_native_prefix(n)) using { n <= 22207u64; }
  apply(adler_small_tail_metadata(n)) using { n <= 22207u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 22207u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 22204u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)) by { simp() using { 0 <= (int32)(uint32)n; (int32)(uint32)n <= 22207; 0 <= (int32)(uint32)(n - n % 4u64); (int32)(uint32)(n - n % 4u64) <= 22204; } }
  apply(int32_subtract_to_integer((int32)(uint32)n, (int32)(uint32)(n - n % 4u64))) using { defined((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)); }
  have to_integer((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)) == to_integer((int32)(uint32)(n % 4u64)) by {
   rewrite(to_integer((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)) == to_integer((int32)(uint32)n) - to_integer((int32)(uint32)(n - n % 4u64)));
   rewrite(to_integer((int32)(uint32)n) == to_integer(n));
   rewrite(to_integer((int32)(uint32)(n % 4u64)) == to_integer(n % 4u64));
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   arithmetic() using { to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64); }
  }
  apply(int32_equal_of_to_integer((int32)(uint32)n - (int32)(uint32)(n - n % 4u64), (int32)(uint32)(n % 4u64))) using { to_integer((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)) == to_integer((int32)(uint32)(n % 4u64)); }
 }
}
