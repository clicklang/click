# Checked full-width metadata and actual iterator steps for general Adler batches.
# The memory/index boundary is explicit: 0..INT32_MAX, never a truncated usize.
# These lemmas do not establish the computation or checksum postcondition.

theorem adler_general_bounded_quotient_bounds(n: Integer, d: Integer) {
 requires 0 <= n;
 requires n <= 2147483647;
 requires 4 <= d;
 requires d != 0;
 ensures 0 <= truncating_quotient(n, d) by {
  have 1 <= d by { arithmetic() using { 4 <= d; } }
  have 0 * d <= n by { arithmetic() using { 0 <= n; } }
  apply(integer_positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; }
 }
 ensures truncating_quotient(n, d) <= 536870911 by {
  have 1 <= d by { arithmetic() using { 4 <= d; } }
  have n < 536870912 * d by { arithmetic() using { n <= 2147483647; 4 <= d; } }
  apply(integer_positive_divisor_quotient_strict_upper(n, d, 536870912)) using { d != 0; 1 <= d; n < 536870912 * d; }
  arithmetic() using { truncating_quotient(n, d) < 536870912; }
 }
}
function adler_general_vector_prefix(n: Integer) -> Integer {
 n - truncating_remainder(n, 4)
}
theorem adler_general_bounded_partition(n: Integer) {
 requires 0 <= n;
 requires n <= 2147483647;
 ensures 0 <= adler_general_vector_prefix(n) and adler_general_vector_prefix(n) <= 2147483644 by {
  apply(integer_truncation_identity(n, 4)) using { 4 != 0; }
  apply(adler_general_bounded_quotient_bounds(n, 4)) using { 0 <= n; n <= 2147483647; 4 <= 4; 4 != 0; }
  unfold(adler_general_vector_prefix(n));
  both {
   arithmetic() using { n == truncating_quotient(n, 4) * 4 + truncating_remainder(n, 4); 0 <= truncating_quotient(n, 4); }
  } and {
   arithmetic() using { n == truncating_quotient(n, 4) * 4 + truncating_remainder(n, 4); truncating_quotient(n, 4) <= 536870911; }
  }
 }
 ensures 0 <= truncating_remainder(n, 4) by {
  apply(integer_nonnegative_dividend_remainder(n, 4)) using { 4 != 0; 0 <= n; }
 }
 ensures truncating_remainder(n, 4) <= 3 by {
  apply(integer_positive_divisor_remainder_upper(n, 4)) using { 4 != 0; 0 < 4; }
 }
}

theorem adler_general_unsigned_bounded_partition(n: uint64) {
 requires n <= 2147483647u64;
 ensures 0 <= to_integer(n - n % 4u64) and to_integer(n - n % 4u64) <= 2147483644 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_partition(to_integer(n))) using { 0 <= to_integer(n); to_integer(n) <= 2147483647; }
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer(n % 4u64) <= to_integer(n) by {
   rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
   have 0 <= to_integer(n) - truncating_remainder(to_integer(n), 4) by {
    unfold(adler_general_vector_prefix(to_integer(n)));
    arithmetic() using { 0 <= adler_general_vector_prefix(to_integer(n)); adler_general_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
   }
   arithmetic() using { 0 <= to_integer(n) - truncating_remainder(to_integer(n), 4); }
  }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  rewrite(to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64));
  rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
  unfold(adler_general_vector_prefix(to_integer(n)));
  both {
   arithmetic() using { 0 <= adler_general_vector_prefix(to_integer(n)); adler_general_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
  } and {
   arithmetic() using { adler_general_vector_prefix(to_integer(n)) <= 2147483644; adler_general_vector_prefix(to_integer(n)) == to_integer(n) - truncating_remainder(to_integer(n), 4); }
  }
 }
}

theorem adler_general_signed_bounded_prefix(n: uint64) {
 requires n <= 2147483647u64;
 ensures 0 <= (int32)(uint32)(n - n % 4u64) and (int32)(uint32)(n - n % 4u64) <= 2147483644 by {
  apply(adler_general_unsigned_bounded_partition(n)) using { n <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  have n - n % 4u64 <= n by { normalize() using { n % 4u64 <= n; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= n; n <= 2147483647u64; } }
  have to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n - n % 4u64) => 0 <= to_integer(n - n % 4u64);
    premise 1: to_integer(n - n % 4u64) <= 2147483644 => to_integer(n - n % 4u64) <= 2147483644;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64);
    conclusion 0;
   }
  }
  have 0 <= to_integer((int32)(uint32)(n - n % 4u64)) by { rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64)); assumption(); }
  have to_integer((int32)(uint32)(n - n % 4u64)) <= 2147483644 by { rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64)); assumption(); }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)(n - n % 4u64))) using { 0 <= to_integer((int32)(uint32)(n - n % 4u64)); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)(n - n % 4u64), 2147483644)) using { to_integer((int32)(uint32)(n - n % 4u64)) <= 2147483644; }
  }
 }
}

theorem adler_general_multiple_of_four(n: Integer) {
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

theorem adler_general_int32_multiple_of_four(n: int32, q: Integer) {
 requires 0 <= q;
 requires to_integer(n) == q * 4;
 ensures n % 4 == 0 by {
  have defined(n % 4) by { normalize(); }
  apply(int32_remainder_to_integer(n, 4)) using { defined(n % 4); to_integer(4) != 0; }
  apply(adler_general_multiple_of_four(q)) using { 0 <= q; }
  have to_integer(n % 4) == 0 by {
   rewrite(to_integer(n % 4) == truncating_remainder(to_integer(n), to_integer(4)));
   rewrite(to_integer(n) == q * 4);
   assumption();
  }
  apply(int32_equal_of_to_integer(n % 4, 0)) using { to_integer(n % 4) == 0; }
 }
}

theorem adler_general_bounded_prefix_divisible(n: uint64) {
 requires n <= 2147483647u64;
 ensures (int32)(uint32)(n - n % 4u64) % 4 == 0 by {
  apply(adler_general_unsigned_bounded_partition(n)) using { n <= 2147483647u64; }
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_quotient_bounds(to_integer(n), 4)) using { 0 <= to_integer(n); to_integer(n) <= 2147483647; 4 <= 4; 4 != 0; }
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
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= n; n <= 2147483647u64; } }
  have to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64) by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n - n % 4u64) => 0 <= to_integer(n - n % 4u64);
    premise 1: to_integer(n - n % 4u64) <= 2147483644 => to_integer(n - n % 4u64) <= 2147483644;
    integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64);
    conclusion 0;
   }
  }
  have to_integer((int32)(uint32)(n - n % 4u64)) == truncating_quotient(to_integer(n), 4) * 4 by {
   rewrite(to_integer((int32)(uint32)(n - n % 4u64)) == to_integer(n - n % 4u64));
   assumption();
  }
  apply(adler_general_int32_multiple_of_four((int32)(uint32)(n - n % 4u64), truncating_quotient(to_integer(n), 4))) using { 0 <= truncating_quotient(to_integer(n), 4); to_integer((int32)(uint32)(n - n % 4u64)) == truncating_quotient(to_integer(n), 4) * 4; }
 }
}

theorem adler_general_uint64_bounded_equality(left: uint64, right: uint64) {
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

theorem adler_general_bounded_tail_metadata(n: uint64) {
 requires n <= 2147483647u64;
 ensures n - (n - n % 4u64) == n % 4u64 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_partition(to_integer(n))) using { 0 <= to_integer(n); to_integer(n) <= 2147483647; }
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
  apply(adler_general_uint64_bounded_equality(n - (n - n % 4u64), n % 4u64)) using { to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64); 0 <= to_integer(n - (n - n % 4u64)); to_integer(n - (n - n % 4u64)) <= 2147483647; 0 <= to_integer(n % 4u64); to_integer(n % 4u64) <= 2147483647; }
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

theorem adler_general_bounded_native_prefix(n: uint64) {
 requires n <= 2147483647u64;
 ensures n - n % 4u64 <= 2147483644u64 by {
  apply(adler_general_unsigned_bounded_partition(n)) using { n <= 2147483647u64; }
  apply(uint64_less_equal_of_to_integer(n - n % 4u64, 2147483644u64)) using { to_integer(n - n % 4u64) <= 2147483644; }
 }
}
theorem adler_general_index_observation(n: uint64) {
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
theorem adler_general_bounded_signed_tail(n: uint64) {
 requires n <= 2147483647u64;
 ensures 0 <= (int32)(uint32)(n % 4u64) and (int32)(uint32)(n % 4u64) <= 3 by {
  apply(adler_general_bounded_tail_metadata(n)) using { n <= 2147483647u64; }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_general_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
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

theorem adler_general_signed_partition_identity(n: uint64) {
 requires n <= 2147483647u64;
 ensures (int32)(uint32)n == (int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64) by {
  apply(adler_general_signed_bounded_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_signed_tail(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_native_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_tail_metadata(n)) using { n <= 2147483647u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 2147483644u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_general_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_general_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)(n - n % 4u64) + (int32)(uint32)(n % 4u64)) by { simp() using { 0 <= (int32)(uint32)(n - n % 4u64); (int32)(uint32)(n - n % 4u64) <= 2147483644; 0 <= (int32)(uint32)(n % 4u64); (int32)(uint32)(n % 4u64) <= 3; } }
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

theorem adler_general_short_integer_remainder(n: Integer, d: Integer) {
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

theorem adler_general_native_bounded_prefix_divisible(n: uint64) {
 requires n <= 2147483647u64;
 ensures (n - n % 4u64) % 4u64 == 0u64 by {
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_quotient_bounds(to_integer(n), 4)) using { 0 <= to_integer(n); to_integer(n) <= 2147483647; 4 <= 4; 4 != 0; }
  apply(adler_general_multiple_of_four(truncating_quotient(to_integer(n), 4))) using { 0 <= truncating_quotient(to_integer(n), 4); }
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
  apply(adler_general_uint64_bounded_equality((n - n % 4u64) % 4u64, 0u64)) using { to_integer((n - n % 4u64) % 4u64) == 0; 0 <= to_integer((n - n % 4u64) % 4u64); to_integer((n - n % 4u64) % 4u64) <= 2147483647; }
 }
}

theorem adler_general_bounded_prefix_within_full(n: uint64) {
 requires n <= 2147483647u64;
 ensures 0 <= (int32)(uint32)n and (int32)(uint32)n <= 2147483647 by {
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  have 0u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, n)) using { 0u64 <= n; }
  apply(uint64_less_equal_to_integer(n, 2147483647u64)) using { n <= 2147483647u64; }
  have 0 <= to_integer((int32)(uint32)n) by { rewrite(to_integer((int32)(uint32)n) == to_integer(n)); assumption(); }
  have to_integer((int32)(uint32)n) <= 2147483647 by { rewrite(to_integer((int32)(uint32)n) == to_integer(n)); simp() using { to_integer(n) <= to_integer(2147483647u64); } }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)n)) using { 0 <= to_integer((int32)(uint32)n); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)n, 2147483647)) using { to_integer((int32)(uint32)n) <= 2147483647; }
  }
 }
 ensures (int32)(uint32)(n - n % 4u64) <= (int32)(uint32)n by {
  apply(adler_general_bounded_native_prefix(n)) using { n <= 2147483647u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 2147483644u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_general_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
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

theorem adler_general_bounded_tail_indices(n: uint64) {
 requires n <= 2147483647u64;
 ensures (int32)(uint32)(n % 4u64) <= (int32)(uint32)n by {
  apply(adler_general_bounded_prefix_within_full(n)) using { n <= 2147483647u64; }
  apply(adler_general_signed_bounded_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_signed_tail(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_native_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_tail_metadata(n)) using { n <= 2147483647u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 2147483644u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_general_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_general_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
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
  apply(adler_general_bounded_prefix_within_full(n)) using { n <= 2147483647u64; }
  apply(adler_general_signed_bounded_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_signed_tail(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_native_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_tail_metadata(n)) using { n <= 2147483647u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 2147483644u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_general_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_general_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)n - (int32)(uint32)(n % 4u64)) by { simp() using { 0 <= (int32)(uint32)n; (int32)(uint32)n <= 2147483647; 0 <= (int32)(uint32)(n % 4u64); (int32)(uint32)(n % 4u64) <= 3; } }
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
  apply(adler_general_bounded_prefix_within_full(n)) using { n <= 2147483647u64; }
  apply(adler_general_signed_bounded_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_signed_tail(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_native_prefix(n)) using { n <= 2147483647u64; }
  apply(adler_general_bounded_tail_metadata(n)) using { n <= 2147483647u64; }
  have n <= 2147483647u64 by { normalize() using { n <= 2147483647u64; } }
  have n - n % 4u64 <= 2147483647u64 by { normalize() using { n - n % 4u64 <= 2147483644u64; } }
  have n % 4u64 <= 2147483647u64 by { normalize() using { n % 4u64 <= 3u64; } }
  apply(adler_general_index_observation(n)) using { n <= 2147483647u64; }
  apply(adler_general_index_observation(n - n % 4u64)) using { n - n % 4u64 <= 2147483647u64; }
  apply(adler_general_index_observation(n % 4u64)) using { n % 4u64 <= 2147483647u64; }
  have n % 4u64 <= n by { normalize(); }
  apply(uint64_less_equal_to_integer(n % 4u64, n)) using { n % 4u64 <= n; }
  apply(uint64_subtract_to_integer(n, n % 4u64)) using { to_integer(n % 4u64) <= to_integer(n); }
  have defined((int32)(uint32)n - (int32)(uint32)(n - n % 4u64)) by { simp() using { 0 <= (int32)(uint32)n; (int32)(uint32)n <= 2147483647; 0 <= (int32)(uint32)(n - n % 4u64); (int32)(uint32)(n - n % 4u64) <= 2147483644; } }
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

theorem adler_aligned_outer_partition(p: Integer) {
 requires 0 <= p;
 requires p <= 2147483644;
 requires truncating_remainder(p, 4) == 0;
 ensures 0 <= truncating_remainder(p, 22208) and truncating_remainder(p, 22208) <= 22204 by {
  apply(integer_truncation_identity(p, 4)) using { 4 != 0; }
  apply(integer_truncation_identity(p, 22208)) using { 22208 != 0; }
  apply(integer_nonnegative_dividend_remainder(p, 22208)) using { 22208 != 0; 0 <= p; }
  apply(integer_positive_divisor_remainder_upper(p, 22208)) using { 22208 != 0; 0 < 22208; }
  have truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4 by {
   arithmetic() using { p == truncating_quotient(p, 4) * 4 + truncating_remainder(p, 4); truncating_remainder(p, 4) == 0; p == truncating_quotient(p, 22208) * 22208 + truncating_remainder(p, 22208); }
  }
  have truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= 5551 by {
   if 5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) {
    have 5552 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) by { arithmetic() using { 5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); } }
    have 22208 <= truncating_remainder(p, 22208) by { arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; 5552 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); } }
    have not (truncating_remainder(p, 22208) <= 22207) by { arithmetic() using { 22208 <= truncating_remainder(p, 22208); } }
    contradiction(truncating_remainder(p, 22208) <= 22207);
   } else {
    arithmetic() using { not (5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)); }
   }
  }
  both { assumption(); } and {
   arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= 5551; }
  }
 }
 ensures truncating_remainder(truncating_remainder(p, 22208), 4) == 0 by {
  apply(integer_truncation_identity(p, 4)) using { 4 != 0; }
  apply(integer_truncation_identity(p, 22208)) using { 22208 != 0; }
  apply(integer_nonnegative_dividend_remainder(p, 22208)) using { 22208 != 0; 0 <= p; }
  have truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4 by {
   arithmetic() using { p == truncating_quotient(p, 4) * 4 + truncating_remainder(p, 4); truncating_remainder(p, 4) == 0; p == truncating_quotient(p, 22208) * 22208 + truncating_remainder(p, 22208); }
  }
  have 0 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) by {
   if truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0 {
    have truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= -1 by { arithmetic() using { truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0; } }
    have truncating_remainder(p, 22208) <= -4 by { arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= -1; } }
    have not (0 <= truncating_remainder(p, 22208)) by { arithmetic() using { truncating_remainder(p, 22208) <= -4; } }
    contradiction(0 <= truncating_remainder(p, 22208));
   } else {
    arithmetic() using { not (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0); }
   }
  }
  apply(adler_general_multiple_of_four(truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208))) using { 0 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); }
  rewrite(truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4);
  assumption();
 }
}

theorem adler_outer_remainder_bounds(p: uint64) {
 requires p <= 2147483644u64;
 requires p % 4u64 == 0u64;
 ensures 0 <= to_integer(p % 22208u64) and to_integer(p % 22208u64) <= 22204 by {
  have 0u64 <= p by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, p)) using { 0u64 <= p; }
  apply(uint64_less_equal_to_integer(p, 2147483644u64)) using { p <= 2147483644u64; }
  apply(uint64_remainder_to_integer(p, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer(p % 4u64) == 0 by { rewrite(p % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p), 4) == 0 by { arithmetic() using { to_integer(p % 4u64) == truncating_remainder(to_integer(p), to_integer(4u64)); to_integer(p % 4u64) == 0; } }
  apply(adler_aligned_outer_partition(to_integer(p))) using { 0 <= to_integer(p); to_integer(p) <= 2147483644; truncating_remainder(to_integer(p), 4) == 0; }
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; }
  rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_outer_remainder_native_bound(p: uint64) {
 requires p <= 2147483644u64;
 requires p % 4u64 == 0u64;
 ensures p % 22208u64 <= 22204u64 by {
  apply(adler_outer_remainder_bounds(p)) using { p <= 2147483644u64; p % 4u64 == 0u64; }
  apply(uint64_less_equal_of_to_integer(p % 22208u64, 22204u64)) using { to_integer(p % 22208u64) <= 22204; }
 }
}

theorem adler_outer_remainder_divisible(p: uint64) {
 requires p <= 2147483644u64;
 requires p % 4u64 == 0u64;
 ensures (p % 22208u64) % 4u64 == 0u64 by {
  have 0u64 <= p by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, p)) using { 0u64 <= p; }
  apply(uint64_less_equal_to_integer(p, 2147483644u64)) using { p <= 2147483644u64; }
  apply(uint64_remainder_to_integer(p, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer(p % 4u64) == 0 by { rewrite(p % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p), 4) == 0 by { arithmetic() using { to_integer(p % 4u64) == truncating_remainder(to_integer(p), to_integer(4u64)); to_integer(p % 4u64) == 0; } }
  apply(adler_aligned_outer_partition(to_integer(p))) using { 0 <= to_integer(p); to_integer(p) <= 2147483644; truncating_remainder(to_integer(p), 4) == 0; }
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; }
  apply(uint64_remainder_to_integer(p % 22208u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer((p % 22208u64) % 4u64) == 0 by {
   rewrite(to_integer((p % 22208u64) % 4u64) == truncating_remainder(to_integer(p % 22208u64), to_integer(4u64)));
   rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
   assumption();
  }
  have 0 <= to_integer((p % 22208u64) % 4u64) by { arithmetic() using { to_integer((p % 22208u64) % 4u64) == 0; } }
  have to_integer((p % 22208u64) % 4u64) <= 2147483647 by { arithmetic() using { to_integer((p % 22208u64) % 4u64) == 0; } }
  apply(adler_general_uint64_bounded_equality((p % 22208u64) % 4u64, 0u64)) using { to_integer((p % 22208u64) % 4u64) == 0; 0 <= to_integer((p % 22208u64) % 4u64); to_integer((p % 22208u64) % 4u64) <= 2147483647; 0 <= to_integer(0u64); to_integer(0u64) <= 2147483647; }
 }
}

theorem adler_u64_index_observation(value: uint64) {
 requires 0 <= to_integer(value);
 requires to_integer(value) <= 2147483647;
 ensures to_integer((int32)(uint32)value) == to_integer(value) and (0 <= (int32)(uint32)value and (int32)(uint32)value <= 2147483647) by {
  have to_integer((int32)(uint32)value) == to_integer(value) by { arithmetic_certificate special {
   premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
   premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)value) == to_integer(value);
   conclusion 0;
  } }
  have 0 <= to_integer((int32)(uint32)value) by { rewrite(to_integer((int32)(uint32)value) == to_integer(value)); assumption(); }
  apply(int32_less_equal_of_to_integer(0, (int32)(uint32)value)) using { 0 <= to_integer((int32)(uint32)value); }
  both { assumption(); } and { both { assumption(); } and { normalize(); } }
 }
}

theorem adler_outer_remainder_signed_bound(p: uint64) {
 requires p <= 2147483644u64;
 requires p % 4u64 == 0u64;
 ensures 0 <= (int32)(uint32)(p % 22208u64) and (int32)(uint32)(p % 22208u64) <= 22204 by {
  apply(adler_outer_remainder_bounds(p)) using { p <= 2147483644u64; p % 4u64 == 0u64; }
  have to_integer(p % 22208u64) <= 2147483647 by { arithmetic() using { to_integer(p % 22208u64) <= 22204; } }
  apply(adler_u64_index_observation(p % 22208u64)) using { 0 <= to_integer(p % 22208u64); to_integer(p % 22208u64) <= 2147483647; }
  have to_integer((int32)(uint32)(p % 22208u64)) <= 22204 by { rewrite(to_integer((int32)(uint32)(p % 22208u64)) == to_integer(p % 22208u64)); assumption(); }
  apply(int32_less_equal_of_to_integer((int32)(uint32)(p % 22208u64), 22204)) using { to_integer((int32)(uint32)(p % 22208u64)) <= 22204; }
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_outer_remainder_signed_divisible(p: uint64) {
 requires p <= 2147483644u64;
 requires p % 4u64 == 0u64;
 ensures ((int32)(uint32)(p % 22208u64)) % 4 == 0 by {
  apply(adler_outer_remainder_divisible(p)) using { p <= 2147483644u64; p % 4u64 == 0u64; }
  apply(adler_outer_remainder_bounds(p)) using { p <= 2147483644u64; p % 4u64 == 0u64; }
  have to_integer(p % 22208u64) <= 2147483647 by { arithmetic() using { to_integer(p % 22208u64) <= 22204; } }
  apply(adler_u64_index_observation(p % 22208u64)) using { 0 <= to_integer(p % 22208u64); to_integer(p % 22208u64) <= 2147483647; }
  apply(uint64_remainder_to_integer(p % 22208u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; }
  have to_integer((p % 22208u64) % 4u64) == 0 by { rewrite((p % 22208u64) % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p % 22208u64), 4) == 0 by { arithmetic() using { to_integer((p % 22208u64) % 4u64) == truncating_remainder(to_integer(p % 22208u64), to_integer(4u64)); to_integer((p % 22208u64) % 4u64) == 0; } }
  have defined(((int32)(uint32)(p % 22208u64)) % 4) by { normalize(); }
  apply(int32_remainder_to_integer((int32)(uint32)(p % 22208u64), 4)) using { defined(((int32)(uint32)(p % 22208u64)) % 4); to_integer(4) != 0; }
  have to_integer(((int32)(uint32)(p % 22208u64)) % 4) == 0 by {
   rewrite(to_integer(((int32)(uint32)(p % 22208u64)) % 4) == truncating_remainder(to_integer((int32)(uint32)(p % 22208u64)), to_integer(4)));
   rewrite(to_integer((int32)(uint32)(p % 22208u64)) == to_integer(p % 22208u64));
   assumption();
  }
  apply(int32_equal_of_to_integer(((int32)(uint32)(p % 22208u64)) % 4, 0)) using { to_integer(((int32)(uint32)(p % 22208u64)) % 4) == 0; }
 }
}

theorem adler_multiple_of_full_batch(n: Integer) {
 requires 0 <= n;
 ensures truncating_remainder(n * 22208, 22208) == 0 by {
  apply(integer_positive_divisor_quotient_lower(n * 22208, 22208, n)) using { 22208 != 0; 1 <= 22208; n * 22208 <= n * 22208; }
  have 0 < n + 1 by { arithmetic() using { 0 <= n; } }
  have n * 22208 < (n + 1) * 22208 by { arithmetic() using {}; }
  apply(integer_positive_divisor_quotient_strict_upper(n * 22208, 22208, n + 1)) using { 22208 != 0; 1 <= 22208; 0 < n + 1; n * 22208 < (n + 1) * 22208; }
  have truncating_quotient(n * 22208, 22208) == n by { arithmetic() using { n <= truncating_quotient(n * 22208, 22208); truncating_quotient(n * 22208, 22208) < n + 1; } }
  apply(integer_truncation_identity(n * 22208, 22208)) using { 22208 != 0; }
  arithmetic() using { n * 22208 == truncating_quotient(n * 22208, 22208) * 22208 + truncating_remainder(n * 22208, 22208); truncating_quotient(n * 22208, 22208) == n; }
 }
}


theorem adler_outer_bulk_observation(p: uint64) {
 requires p <= 2147483644u64;
 ensures 0 <= to_integer(p - p % 22208u64) and to_integer(p - p % 22208u64) <= 2147483644 by {
  have p % 22208u64 <= p by { normalize(); }
  have 0u64 <= p % 22208u64 by { normalize(); }
  apply(uint64_less_equal_to_integer(p % 22208u64, p)) using { p % 22208u64 <= p; }
  apply(uint64_less_equal_to_integer(0u64, p % 22208u64)) using { 0u64 <= p % 22208u64; }
  apply(uint64_less_equal_to_integer(p, 2147483644u64)) using { p <= 2147483644u64; }
  apply(uint64_subtract_to_integer(p, p % 22208u64)) using { to_integer(p % 22208u64) <= to_integer(p); }
  rewrite(to_integer(p - p % 22208u64) == to_integer(p) - to_integer(p % 22208u64));
  both {
   arithmetic() using { to_integer(p % 22208u64) <= to_integer(p); }
  } and {
   arithmetic() using { to_integer(p) <= 2147483644; 0 <= to_integer(p % 22208u64); }
  }
 }
}

theorem adler_outer_bulk_signed(p: uint64) {
 requires p <= 2147483644u64;
 ensures 0 <= (int32)(uint32)(p - p % 22208u64) and (int32)(uint32)(p - p % 22208u64) <= 2147483644 by {
  apply(adler_outer_bulk_observation(p)) using { p <= 2147483644u64; }
  have to_integer(p - p % 22208u64) <= 2147483647 by { arithmetic() using { to_integer(p - p % 22208u64) <= 2147483644; } }
  apply(adler_u64_index_observation(p - p % 22208u64)) using { 0 <= to_integer(p - p % 22208u64); to_integer(p - p % 22208u64) <= 2147483647; }
  have to_integer((int32)(uint32)(p - p % 22208u64)) <= 2147483644 by { rewrite(to_integer((int32)(uint32)(p - p % 22208u64)) == to_integer(p - p % 22208u64)); assumption(); }
  apply(int32_less_equal_of_to_integer((int32)(uint32)(p - p % 22208u64), 2147483644)) using { to_integer((int32)(uint32)(p - p % 22208u64)) <= 2147483644; }
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_outer_bulk_multiple(p: uint64) {
 requires p <= 2147483644u64;
 ensures to_integer(p - p % 22208u64) == truncating_quotient(to_integer(p), 22208) * 22208 by {
  have p % 22208u64 <= p by { normalize(); }
  apply(uint64_less_equal_to_integer(p % 22208u64, p)) using { p % 22208u64 <= p; }
  apply(uint64_subtract_to_integer(p, p % 22208u64)) using { to_integer(p % 22208u64) <= to_integer(p); }
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; }
  apply(integer_truncation_identity(to_integer(p), 22208)) using { 22208 != 0; }
  rewrite(to_integer(p - p % 22208u64) == to_integer(p) - to_integer(p % 22208u64));
  rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
  arithmetic() using { to_integer(p) == truncating_quotient(to_integer(p), 22208) * 22208 + truncating_remainder(to_integer(p), 22208); }
 }
}

theorem adler_outer_bulk_signed_multiple(p: uint64) {
 requires p <= 2147483644u64;
 ensures ((int32)(uint32)(p - p % 22208u64)) % 22208 == 0 by {
  apply(adler_outer_bulk_observation(p)) using { p <= 2147483644u64; }
  have to_integer(p - p % 22208u64) <= 2147483647 by { arithmetic() using { to_integer(p - p % 22208u64) <= 2147483644; } }
  apply(adler_u64_index_observation(p - p % 22208u64)) using { 0 <= to_integer(p - p % 22208u64); to_integer(p - p % 22208u64) <= 2147483647; }
  apply(adler_outer_bulk_multiple(p)) using { p <= 2147483644u64; }
  have 0u64 <= p by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, p)) using { 0u64 <= p; }
  have 0 * 22208 <= to_integer(p) by { arithmetic() using { 0 <= to_integer(p); } }
  apply(integer_positive_divisor_quotient_lower(to_integer(p), 22208, 0)) using { 22208 != 0; 1 <= 22208; 0 * 22208 <= to_integer(p); }
  apply(adler_multiple_of_full_batch(truncating_quotient(to_integer(p), 22208))) using { 0 <= truncating_quotient(to_integer(p), 22208); }
  have defined(((int32)(uint32)(p - p % 22208u64)) % 22208) by { normalize(); }
  apply(int32_remainder_to_integer((int32)(uint32)(p - p % 22208u64), 22208)) using { defined(((int32)(uint32)(p - p % 22208u64)) % 22208); to_integer(22208) != 0; }
  have to_integer(((int32)(uint32)(p - p % 22208u64)) % 22208) == 0 by {
   rewrite(to_integer(((int32)(uint32)(p - p % 22208u64)) % 22208) == truncating_remainder(to_integer((int32)(uint32)(p - p % 22208u64)), to_integer(22208)));
   rewrite(to_integer((int32)(uint32)(p - p % 22208u64)) == to_integer(p - p % 22208u64));
   rewrite(to_integer(p - p % 22208u64) == truncating_quotient(to_integer(p), 22208) * 22208);
   assumption();
  }
  apply(int32_equal_of_to_integer(((int32)(uint32)(p - p % 22208u64)) % 22208, 0)) using { to_integer(((int32)(uint32)(p - p % 22208u64)) % 22208) == 0; }
 }
}

theorem adler_outer_nonempty_remaining(remaining: int32) {
 requires 0 < remaining;
 requires remaining % 22208 == 0;
 ensures 22208 <= remaining by {
  have 0 <= remaining by { arithmetic() using { 0 < remaining; } }
  if remaining < 22208 {
   have remaining % 22208 == remaining by { normalize() using { 0 <= remaining; remaining < 22208; } }
   have remaining == 0 by { simp() using { remaining % 22208 == 0; remaining % 22208 == remaining; } }
   have not (0 < remaining) by { arithmetic() using { remaining == 0; } }
   contradiction(0 < remaining);
  } else {
   simp();
  }
 }
}

theorem adler_outer_remaining_step(total: int32, remaining: int32) {
 requires 0 <= total;
 requires remaining <= total;
 requires 22208 <= remaining;
 ensures defined(remaining - 22208) by {
  apply(int32_nonnegative_subtract_within_value_is_defined(remaining, 22208)) using { 0 <= 22208; 22208 <= remaining; }
 }
 ensures 0 <= remaining - 22208 and remaining - 22208 <= total by {
  apply(int32_nonnegative_subtract_within_value_is_defined(remaining, 22208)) using { 0 <= 22208; 22208 <= remaining; }
  both {
   arithmetic() using { 22208 <= remaining; }
  } and {
   arithmetic() using { remaining <= total; 22208 <= remaining; }
  }
 }
 ensures remaining - 22208 < remaining by {
  apply(int32_nonnegative_subtract_within_value_is_defined(remaining, 22208)) using { 0 <= 22208; 22208 <= remaining; }
  arithmetic() using { 22208 <= remaining; }
 }
}

theorem adler_outer_remaining_step_divisible(remaining: int32) {
 requires 22208 <= remaining;
 requires remaining % 22208 == 0;
 ensures (remaining - 22208) % 22208 == 0 by {
  apply(int32_nonnegative_subtract_within_value_is_defined(remaining, 22208)) using { 0 <= 22208; 22208 <= remaining; }
  apply(int32_subtract_to_integer(remaining, 22208)) using { defined(remaining - 22208); }
  apply(int32_less_equal_to_integer(22208, remaining)) using { 22208 <= remaining; }
  have defined(remaining % 22208) by { normalize(); }
  apply(int32_remainder_to_integer(remaining, 22208)) using { defined(remaining % 22208); to_integer(22208) != 0; }
  have to_integer(remaining % 22208) == 0 by { rewrite(remaining % 22208 == 0); normalize(); }
  have truncating_remainder(to_integer(remaining), 22208) == 0 by { arithmetic() using { to_integer(remaining % 22208) == truncating_remainder(to_integer(remaining), to_integer(22208)); to_integer(remaining % 22208) == 0; } }
  apply(integer_truncation_identity(to_integer(remaining), 22208)) using { 22208 != 0; }
  have 1 * 22208 <= to_integer(remaining) by { arithmetic() using { 22208 <= to_integer(remaining); } }
  apply(integer_positive_divisor_quotient_lower(to_integer(remaining), 22208, 1)) using { 22208 != 0; 1 <= 22208; 1 * 22208 <= to_integer(remaining); }
  have 0 <= truncating_quotient(to_integer(remaining), 22208) - 1 by { arithmetic() using { 1 <= truncating_quotient(to_integer(remaining), 22208); } }
  apply(adler_multiple_of_full_batch(truncating_quotient(to_integer(remaining), 22208) - 1)) using { 0 <= truncating_quotient(to_integer(remaining), 22208) - 1; }
  have to_integer(remaining - 22208) == (truncating_quotient(to_integer(remaining), 22208) - 1) * 22208 by {
   arithmetic() using { to_integer(remaining - 22208) == to_integer(remaining) - to_integer(22208); to_integer(remaining) == truncating_quotient(to_integer(remaining), 22208) * 22208 + truncating_remainder(to_integer(remaining), 22208); truncating_remainder(to_integer(remaining), 22208) == 0; }
  }
  have defined((remaining - 22208) % 22208) by { normalize() using { defined(remaining - 22208); } }
  apply(int32_remainder_to_integer(remaining - 22208, 22208)) using { defined((remaining - 22208) % 22208); to_integer(22208) != 0; }
  have to_integer((remaining - 22208) % 22208) == 0 by {
   rewrite(to_integer((remaining - 22208) % 22208) == truncating_remainder(to_integer(remaining - 22208), to_integer(22208)));
   rewrite(to_integer(remaining - 22208) == (truncating_quotient(to_integer(remaining), 22208) - 1) * 22208);
   assumption();
  }
  apply(int32_equal_of_to_integer((remaining - 22208) % 22208, 0)) using { to_integer((remaining - 22208) % 22208) == 0; }
 }
}

# Compose a batch start and the actual inner cursor displacement in the
# original input coordinates. Every native sum has a checked Integer bridge.
theorem adler_absolute_chunk_access(t: int32, pos: int32, n: int32) {
 requires 0 <= t;
 requires t <= 2147461439;
 requires 0 <= pos;
 requires pos <= 22204;
 requires t + 22208 <= n;
 requires 0 <= n;
 ensures 0 <= t + pos by { arithmetic() using { 0 <= t; t <= 2147461439; 0 <= pos; pos <= 22204; } }
 ensures (t + pos) + 4 <= n by {
  have 0 <= t + pos by { arithmetic() using { 0 <= t; t <= 2147461439; 0 <= pos; pos <= 22204; } }
  have t + pos <= 2147483643 by { arithmetic() using { 0 <= t; t <= 2147461439; 0 <= pos; pos <= 22204; } }
  have defined(t + pos) by { simp() using { 0 <= t; t <= 2147461439; 0 <= pos; pos <= 22204; } }
  apply(int32_less_equal_to_integer(0, t + pos)) using { 0 <= t + pos; }
  apply(int32_less_equal_to_integer(t + pos, 2147483643)) using { t + pos <= 2147483643; }
  have to_integer(t + pos) + to_integer(4) >= -2147483648 by { arithmetic() using { to_integer(0) <= to_integer(t + pos); } }
  have to_integer(t + pos) + to_integer(4) <= 2147483647 by { arithmetic() using { to_integer(t + pos) <= to_integer(2147483643); } }
  apply(int32_add_defined_by_integer_bounds(t + pos, 4)) using { to_integer(t + pos) + to_integer(4) >= -2147483648; to_integer(t + pos) + to_integer(4) <= 2147483647; }
  have defined((t + pos) + 4) by { both { assumption(); } and { assumption(); } }
  have defined(t + 22208) by { simp() using { 0 <= t; t <= 2147461439; } }
  apply(int32_add_to_integer(t, pos)) using { defined(t + pos); }
  apply(int32_add_to_integer(t + pos, 4)) using { defined((t + pos) + 4); }
  apply(int32_add_to_integer(t, 22208)) using { defined(t + 22208); }
  apply(int32_less_equal_to_integer(t + 22208, n)) using { t + 22208 <= n; }
  apply(int32_less_equal_to_integer(pos, 22204)) using { pos <= 22204; }
  have to_integer((t + pos) + 4) <= to_integer(n) by {
   arithmetic() using {
    to_integer(t + pos) == to_integer(t) + to_integer(pos);
    to_integer((t + pos) + 4) == to_integer(t + pos) + to_integer(4);
    to_integer(t + 22208) == to_integer(t) + to_integer(22208);
    to_integer(t + 22208) <= to_integer(n);
    to_integer(pos) <= to_integer(22204);
   }
  }
  apply(int32_less_equal_of_to_integer((t + pos) + 4, n)) using { to_integer((t + pos) + 4) <= to_integer(n); }
 }
}
