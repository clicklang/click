import click::integer;

// Checked partition metadata and actual iterator steps for general Adler batches.
// Batch-local positions (at most 22,208 bytes) are int32; the outer metadata
// below keeps its full uint64 width, never a truncated usize.
// These lemmas do not establish the computation or checksum postcondition.

theorem adler_general_multiple_of_four(n: Integer) {
 requires 0 <= n;
 ensures truncating_remainder(n * 4, 4) == 0 by {
  apply(integer_positive_divisor_quotient_lower(n * 4, 4, n)) using { 4 != 0; 1 <= 4; n * 4 <= n * 4; };
  have 0 < n + 1 by arithmetic() using { 0 <= n; };
  have n * 4 < (n + 1) * 4 by arithmetic() using {};
  apply(integer_positive_divisor_quotient_strict_upper(n * 4, 4, n + 1)) using { 4 != 0; 1 <= 4; 0 < n + 1; n * 4 < (n + 1) * 4; };
  have truncating_quotient(n * 4, 4) == n by arithmetic() using { n <= truncating_quotient(n * 4, 4); truncating_quotient(n * 4, 4) < n + 1; };
  apply(integer_truncation_identity(n * 4, 4)) using { 4 != 0; };
  arithmetic() using { n * 4 == truncating_quotient(n * 4, 4) * 4 + truncating_remainder(n * 4, 4); truncating_quotient(n * 4, 4) == n; };
 }
}

theorem adler_general_short_integer_remainder(n: Integer, d: Integer) {
 requires 0 <= n;
 requires n < d;
 requires 1 <= d;
 requires d != 0;
 ensures truncating_remainder(n, d) == n by {
  have 0 * d <= n by arithmetic() using { 0 <= n; };
  have n < 1 * d by arithmetic() using { n < d; };
  apply(integer_positive_divisor_quotient_lower(n, d, 0)) using { d != 0; 1 <= d; 0 * d <= n; };
  apply(integer_positive_divisor_quotient_strict_upper(n, d, 1)) using { d != 0; 1 <= d; n < 1 * d; };
  have truncating_quotient(n, d) == 0 by arithmetic() using { 0 <= truncating_quotient(n, d); truncating_quotient(n, d) < 1; };
  apply(integer_truncation_identity(n, d)) using { d != 0; };
  have truncating_quotient(n, d) * d == 0 by { rewrite(truncating_quotient(n, d) == 0); normalize(); }
  arithmetic() using { n == truncating_quotient(n, d) * d + truncating_remainder(n, d); truncating_quotient(n, d) * d == 0; };
 }
}

theorem adler_u64_index_observation(value: uint64) {
 requires 0 <= to_integer(value);
 requires to_integer(value) <= 2147483647;
 ensures to_integer((int32)(uint32)value) == to_integer(value) and (0 <= (int32)(uint32)value and (int32)(uint32)value <= 2147483647) by {
  have to_integer((int32)(uint32)value) == to_integer(value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value) => 0 <= to_integer(value);
   premise 1: to_integer(value) <= 2147483647 => to_integer(value) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)value) == to_integer(value);
   conclusion 0;
  } }
  have 0 <= to_integer((int32)(uint32)value) by { rewrite(to_integer((int32)(uint32)value) == to_integer(value)); assumption(); }
  both { assumption(); } and { both { assumption(); } and { normalize(); } }
 }
}

theorem adler_multiple_of_full_batch(n: Integer) {
 requires 0 <= n;
 ensures truncating_remainder(n * 22208, 22208) == 0 by {
  apply(integer_positive_divisor_quotient_lower(n * 22208, 22208, n)) using { 22208 != 0; 1 <= 22208; n * 22208 <= n * 22208; };
  have 0 < n + 1 by arithmetic() using { 0 <= n; };
  have n * 22208 < (n + 1) * 22208 by arithmetic() using {};
  apply(integer_positive_divisor_quotient_strict_upper(n * 22208, 22208, n + 1)) using { 22208 != 0; 1 <= 22208; 0 < n + 1; n * 22208 < (n + 1) * 22208; };
  have truncating_quotient(n * 22208, 22208) == n by arithmetic() using { n <= truncating_quotient(n * 22208, 22208); truncating_quotient(n * 22208, 22208) < n + 1; };
  apply(integer_truncation_identity(n * 22208, 22208)) using { 22208 != 0; };
  arithmetic() using { n * 22208 == truncating_quotient(n * 22208, 22208) * 22208 + truncating_remainder(n * 22208, 22208); truncating_quotient(n * 22208, 22208) == n; };
 }
}

theorem adler_current_window(total: int32, remaining: int32) {
 requires 0 <= total;
 requires total <= 22204;
 requires 0 <= remaining;
 requires remaining <= total;
 ensures defined(total - remaining - 4) and defined((total - remaining - 4) + 4) and to_integer((total - remaining - 4) + 4) <= to_integer(total) by {
  have defined(total - remaining) by auto();
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining) by auto();
  have 0 <= to_integer(total - remaining) by { rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining)); arithmetic() using { to_integer(remaining) <= to_integer(total); }; }
  have to_integer(total - remaining) <= 22204 by { rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining)); arithmetic() using { to_integer(0) <= to_integer(remaining); to_integer(total) <= to_integer(22204); }; }
  have to_integer(total - remaining) - to_integer(4) >= -2147483648 by arithmetic() using { 0 <= to_integer(total - remaining); };
  have to_integer(total - remaining) - to_integer(4) <= 2147483647 by arithmetic() using { to_integer(total - remaining) <= 22204; };
  have defined(total - remaining - 4) by { both { assumption(); } and { assumption(); } }
  have to_integer((total - remaining) - 4) == to_integer((total - remaining)) - to_integer(4) by auto();
  have to_integer(total - remaining - 4) + to_integer(4) >= -2147483648 by { rewrite(to_integer(total - remaining - 4) == to_integer(total - remaining) - to_integer(4)); arithmetic() using { 0 <= to_integer(total - remaining); }; }
  have to_integer(total - remaining - 4) + to_integer(4) <= 2147483647 by { rewrite(to_integer(total - remaining - 4) == to_integer(total - remaining) - to_integer(4)); arithmetic() using { to_integer(total - remaining) <= 22204; }; }
  have defined((total - remaining - 4) + 4) by { both { assumption(); } and { assumption(); } }
  have to_integer((total - remaining - 4) + 4) == to_integer((total - remaining - 4)) + to_integer(4) by auto();
  have to_integer((total - remaining - 4) + 4) <= to_integer(total) by {
   rewrite(to_integer((total - remaining - 4) + 4) == to_integer(total - remaining - 4) + to_integer(4));
   rewrite(to_integer(total - remaining - 4) == to_integer(total - remaining) - to_integer(4));
   rewrite(to_integer(total - remaining) == to_integer(total) - to_integer(remaining));
   arithmetic() using { to_integer(0) <= to_integer(remaining); };
  }
  both { both { assumption(); } and { assumption(); } } and { assumption(); }
 }
}

theorem adler_full_batch_within_advance(remaining: int32) {
 requires 0 <= remaining;
 requires remaining <= 22204;
 ensures to_integer((22208 - remaining - 4) + 4) == to_integer(22208 - remaining) by arithmetic() using { 0 <= remaining; remaining <= 22204; };
}

// Full-width (uint64) partition facts for the per-batch general proof.
// They need no signed-range bound: each is proved through exact Integers.

theorem adler_aligned_outer_partition_u64(p: Integer) {
 requires 0 <= p;
 requires truncating_remainder(p, 4) == 0;
 ensures 0 <= truncating_remainder(p, 22208) and truncating_remainder(p, 22208) <= 22204 by {
  apply(integer_truncation_identity(p, 4)) using { 4 != 0; };
  apply(integer_truncation_identity(p, 22208)) using { 22208 != 0; };
  apply(integer_nonnegative_dividend_remainder(p, 22208)) using { 22208 != 0; 0 <= p; };
  apply(integer_positive_divisor_remainder_upper(p, 22208)) using { 22208 != 0; 0 < 22208; };
  have truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4 by arithmetic() using { p == truncating_quotient(p, 4) * 4 + truncating_remainder(p, 4); truncating_remainder(p, 4) == 0; p == truncating_quotient(p, 22208) * 22208 + truncating_remainder(p, 22208); };
  have truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= 5551 by {
   if 5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) {
    have 5552 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) by arithmetic() using { 5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); };
    have 22208 <= truncating_remainder(p, 22208) by arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; 5552 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); };
    have not (truncating_remainder(p, 22208) <= 22207) by arithmetic() using { 22208 <= truncating_remainder(p, 22208); };
    contradiction(truncating_remainder(p, 22208) <= 22207);
   } else {
    arithmetic() using { not (5551 < truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)); };
   }
  }
  both { assumption(); } and {
   arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= 5551; };
  }
 }
 ensures truncating_remainder(truncating_remainder(p, 22208), 4) == 0 by {
  apply(integer_truncation_identity(p, 4)) using { 4 != 0; };
  apply(integer_truncation_identity(p, 22208)) using { 22208 != 0; };
  apply(integer_nonnegative_dividend_remainder(p, 22208)) using { 22208 != 0; 0 <= p; };
  have truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4 by arithmetic() using { p == truncating_quotient(p, 4) * 4 + truncating_remainder(p, 4); truncating_remainder(p, 4) == 0; p == truncating_quotient(p, 22208) * 22208 + truncating_remainder(p, 22208); };
  have 0 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) by {
   if truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0 {
    have truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= -1 by arithmetic() using { truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0; };
    have truncating_remainder(p, 22208) <= -4 by arithmetic() using { truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4; truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) <= -1; };
    have not (0 <= truncating_remainder(p, 22208)) by arithmetic() using { truncating_remainder(p, 22208) <= -4; };
    contradiction(0 <= truncating_remainder(p, 22208));
   } else {
    arithmetic() using { not (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208) < 0); };
   }
  }
  apply(adler_general_multiple_of_four(truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208))) using { 0 <= truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208); };
  rewrite(truncating_remainder(p, 22208) == (truncating_quotient(p, 4) - 5552 * truncating_quotient(p, 22208)) * 4);
  assumption();
 }
}

theorem adler_general_prefix_divisible_u64(n: uint64) {
 ensures (n - n % 4u64) % 4u64 == 0u64 by {
  have 0u64 <= n by normalize();
  apply(integer_positive_divisor_quotient_lower(to_integer(n), 4, 0)) using { 4 != 0; 1 <= 4; 0 * 4 <= to_integer(n); };
  apply(adler_general_multiple_of_four(truncating_quotient(to_integer(n), 4))) using { 0 <= truncating_quotient(to_integer(n), 4); };
  apply(integer_truncation_identity(to_integer(n), 4)) using { 4 != 0; };
  have n % 4u64 <= n by normalize();
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer(n - (n % 4u64)) == to_integer(n) - to_integer((n % 4u64)) by auto();
  have to_integer(n - n % 4u64) == truncating_quotient(to_integer(n), 4) * 4 by {
   rewrite(to_integer(n - n % 4u64) == to_integer(n) - to_integer(n % 4u64));
   rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64)));
   arithmetic() using { to_integer(n) == truncating_quotient(to_integer(n), 4) * 4 + truncating_remainder(to_integer(n), 4); };
  }
  apply(uint64_remainder_to_integer(n - n % 4u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer((n - n % 4u64) % 4u64) == to_integer(0u64) by {
   rewrite(to_integer((n - n % 4u64) % 4u64) == truncating_remainder(to_integer(n - n % 4u64), to_integer(4u64)));
   rewrite(to_integer(n - n % 4u64) == truncating_quotient(to_integer(n), 4) * 4);
   normalize() using { truncating_remainder(truncating_quotient(to_integer(n), 4) * 4, 4) == 0; };
  }
  assumption();
 }
}

theorem adler_outer_remainder_bounds_u64(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures p % 22208u64 <= 22204u64 by {
  have 0u64 <= p by normalize();
  apply(uint64_remainder_to_integer(p, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer(p % 4u64) == 0 by { rewrite(p % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p), 4) == 0 by arithmetic() using { to_integer(p % 4u64) == truncating_remainder(to_integer(p), to_integer(4u64)); to_integer(p % 4u64) == 0; };
  apply(adler_aligned_outer_partition_u64(to_integer(p))) using { 0 <= to_integer(p); truncating_remainder(to_integer(p), 4) == 0; };
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have to_integer(p % 22208u64) <= to_integer(22204u64) by {
   rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
   arithmetic() using { truncating_remainder(to_integer(p), 22208) <= 22204; };
  }
  assumption();
 }
 ensures (p % 22208u64) % 4u64 == 0u64 by {
  have 0u64 <= p by normalize();
  apply(uint64_remainder_to_integer(p, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer(p % 4u64) == 0 by { rewrite(p % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p), 4) == 0 by arithmetic() using { to_integer(p % 4u64) == truncating_remainder(to_integer(p), to_integer(4u64)); to_integer(p % 4u64) == 0; };
  apply(adler_aligned_outer_partition_u64(to_integer(p))) using { 0 <= to_integer(p); truncating_remainder(to_integer(p), 4) == 0; };
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  apply(uint64_remainder_to_integer(p % 22208u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer((p % 22208u64) % 4u64) == to_integer(0u64) by {
   rewrite(to_integer((p % 22208u64) % 4u64) == truncating_remainder(to_integer(p % 22208u64), to_integer(4u64)));
   rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
   normalize() using { truncating_remainder(truncating_remainder(to_integer(p), 22208), 4) == 0; };
  }
  assumption();
 }
}

theorem adler_outer_bulk_divisible_u64(p: uint64) {
 ensures (p - p % 22208u64) % 22208u64 == 0u64 by {
  have 0u64 <= p by normalize();
  apply(integer_positive_divisor_quotient_lower(to_integer(p), 22208, 0)) using { 22208 != 0; 1 <= 22208; to_integer(0 * 22208) <= to_integer(p); };
  apply(adler_multiple_of_full_batch(truncating_quotient(to_integer(p), 22208))) using { 0 <= truncating_quotient(to_integer(p), 22208); };
  apply(integer_truncation_identity(to_integer(p), 22208)) using { 22208 != 0; };
  have p % 22208u64 <= p by normalize();
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have to_integer(p - (p % 22208u64)) == to_integer(p) - to_integer((p % 22208u64)) by auto();
  have to_integer(p - p % 22208u64) == truncating_quotient(to_integer(p), 22208) * 22208 by {
   rewrite(to_integer(p - p % 22208u64) == to_integer(p) - to_integer(p % 22208u64));
   rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
   arithmetic() using { to_integer(p) == truncating_quotient(to_integer(p), 22208) * 22208 + truncating_remainder(to_integer(p), 22208); };
  }
  apply(uint64_remainder_to_integer(p - p % 22208u64, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have to_integer((p - p % 22208u64) % 22208u64) == to_integer(0u64) by {
   rewrite(to_integer((p - p % 22208u64) % 22208u64) == truncating_remainder(to_integer(p - p % 22208u64), to_integer(22208u64)));
   rewrite(to_integer(p - p % 22208u64) == truncating_quotient(to_integer(p), 22208) * 22208);
   normalize() using { truncating_remainder(truncating_quotient(to_integer(p), 22208) * 22208, 22208) == 0; };
  }
  assumption();
 }
}

theorem adler_outer_remaining_step_divisible_u64(remaining: uint64) {
 requires 22208u64 <= remaining;
 requires remaining % 22208u64 == 0u64;
 ensures (remaining - 22208u64) % 22208u64 == 0u64 by {
  apply(uint64_remainder_to_integer(remaining, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have truncating_remainder(to_integer(remaining), 22208) == 0 by {
   rewrite(truncating_remainder(to_integer(remaining), 22208) == truncating_remainder(to_integer(remaining), to_integer(22208u64)));
   rewrite(truncating_remainder(to_integer(remaining), to_integer(22208u64)) == to_integer(remaining % 22208u64));
   rewrite(remaining % 22208u64 == 0u64);
   normalize();
  }
  apply(integer_truncation_identity(to_integer(remaining), 22208)) using { 22208 != 0; };
  have to_integer(remaining) == truncating_quotient(to_integer(remaining), 22208) * 22208 by arithmetic() using { to_integer(remaining) == truncating_quotient(to_integer(remaining), 22208) * 22208 + truncating_remainder(to_integer(remaining), 22208); truncating_remainder(to_integer(remaining), 22208) == 0; };
  apply(integer_positive_divisor_quotient_lower(to_integer(remaining), 22208, 1)) using { 22208 != 0; 1 <= 22208; to_integer(1 * 22208) <= to_integer(remaining); };
  have 0 <= truncating_quotient(to_integer(remaining), 22208) - 1 by arithmetic() using { 1 <= truncating_quotient(to_integer(remaining), 22208); };
  apply(adler_multiple_of_full_batch(truncating_quotient(to_integer(remaining), 22208) - 1)) using { 0 <= truncating_quotient(to_integer(remaining), 22208) - 1; };
  have to_integer(remaining - 22208u64) == to_integer(remaining) - to_integer(22208u64) by auto();
  have to_integer(remaining - 22208u64) == (truncating_quotient(to_integer(remaining), 22208) - 1) * 22208 by arithmetic() using { to_integer(remaining - 22208u64) == to_integer(remaining) - to_integer(22208u64); to_integer(remaining) == truncating_quotient(to_integer(remaining), 22208) * 22208; };
  apply(uint64_remainder_to_integer(remaining - 22208u64, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  have to_integer((remaining - 22208u64) % 22208u64) == to_integer(0u64) by {
   rewrite(to_integer((remaining - 22208u64) % 22208u64) == truncating_remainder(to_integer(remaining - 22208u64), to_integer(22208u64)));
   rewrite(to_integer(remaining - 22208u64) == (truncating_quotient(to_integer(remaining), 22208) - 1) * 22208);
   normalize() using { truncating_remainder((truncating_quotient(to_integer(remaining), 22208) - 1) * 22208, 22208) == 0; };
  }
  assumption();
 }
}

theorem adler_outer_exhausted_remaining_u64(remaining: uint64) {
 requires remaining < 22208u64;
 requires remaining % 22208u64 == 0u64;
 ensures remaining == 0u64 by {
  have to_integer(remaining) <= 18446744073709551615 by auto();
  apply(adler_general_short_integer_remainder(to_integer(remaining), 22208)) using { 0 <= to_integer(remaining); to_integer(remaining) < 22208; 1 <= 22208; 22208 != 0; };
  have to_integer(remaining % 22208u64) == truncating_remainder(to_integer(remaining), to_integer(22208u64)) by auto();
  have to_integer(remaining) == to_integer(0u64) by {
   rewrite(to_integer(remaining) == truncating_remainder(to_integer(remaining), 22208));
   rewrite(truncating_remainder(to_integer(remaining), 22208) == truncating_remainder(to_integer(remaining), to_integer(22208u64)));
   rewrite(truncating_remainder(to_integer(remaining), to_integer(22208u64)) == to_integer(remaining % 22208u64));
   rewrite(remaining % 22208u64 == 0u64);
   normalize();
  }
  assumption();
 }
}


theorem adler_outer_remainder_integer_bounds_u64(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures 0 <= to_integer(p % 22208u64) and to_integer(p % 22208u64) <= 22204 by {
  have 0u64 <= p by normalize();
  apply(uint64_remainder_to_integer(p, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer(p % 4u64) == 0 by { rewrite(p % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p), 4) == 0 by arithmetic() using { to_integer(p % 4u64) == truncating_remainder(to_integer(p), to_integer(4u64)); to_integer(p % 4u64) == 0; };
  apply(adler_aligned_outer_partition_u64(to_integer(p))) using { 0 <= to_integer(p); truncating_remainder(to_integer(p), 4) == 0; };
  apply(uint64_remainder_to_integer(p, 22208u64)) using { 22208u64 != 0u64; to_integer(22208u64) != 0; };
  rewrite(to_integer(p % 22208u64) == truncating_remainder(to_integer(p), to_integer(22208u64)));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_outer_remainder_signed_bound_u64(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures 0 <= (int32)(uint32)(p % 22208u64) and (int32)(uint32)(p % 22208u64) <= 22204 by {
  apply(adler_outer_remainder_integer_bounds_u64(p)) using { p % 4u64 == 0u64; };
  have to_integer(p % 22208u64) <= 2147483647 by arithmetic() using { to_integer(p % 22208u64) <= 22204; };
  apply(adler_u64_index_observation(p % 22208u64)) using { 0 <= to_integer(p % 22208u64); to_integer(p % 22208u64) <= 2147483647; };
  have to_integer((int32)(uint32)(p % 22208u64)) <= 22204 by { rewrite(to_integer((int32)(uint32)(p % 22208u64)) == to_integer(p % 22208u64)); assumption(); }
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_outer_remainder_signed_divisible_u64(p: uint64) {
 requires p % 4u64 == 0u64;
 ensures ((int32)(uint32)(p % 22208u64)) % 4 == 0 by {
  apply(adler_outer_remainder_bounds_u64(p)) using { p % 4u64 == 0u64; };
  apply(adler_outer_remainder_integer_bounds_u64(p)) using { p % 4u64 == 0u64; };
  have to_integer(p % 22208u64) <= 2147483647 by arithmetic() using { to_integer(p % 22208u64) <= 22204; };
  apply(adler_u64_index_observation(p % 22208u64)) using { 0 <= to_integer(p % 22208u64); to_integer(p % 22208u64) <= 2147483647; };
  apply(uint64_remainder_to_integer(p % 22208u64, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  have to_integer((p % 22208u64) % 4u64) == 0 by { rewrite((p % 22208u64) % 4u64 == 0u64); normalize(); }
  have truncating_remainder(to_integer(p % 22208u64), 4) == 0 by arithmetic() using { to_integer((p % 22208u64) % 4u64) == truncating_remainder(to_integer(p % 22208u64), to_integer(4u64)); to_integer((p % 22208u64) % 4u64) == 0; };
  have defined(((int32)(uint32)(p % 22208u64)) % 4) by normalize();
  apply(int32_remainder_to_integer((int32)(uint32)(p % 22208u64), 4)) using { defined(((int32)(uint32)(p % 22208u64)) % 4); to_integer(4) != 0; };
  have to_integer(((int32)(uint32)(p % 22208u64)) % 4) == 0 by {
   rewrite(to_integer(((int32)(uint32)(p % 22208u64)) % 4) == truncating_remainder(to_integer((int32)(uint32)(p % 22208u64)), to_integer(4)));
   rewrite(to_integer((int32)(uint32)(p % 22208u64)) == to_integer(p % 22208u64));
   assumption();
  }
  assumption();
 }
}

theorem adler_general_tail_metadata_u64(n: uint64) {
 ensures to_integer(n - (n - n % 4u64)) == to_integer(n % 4u64) by normalize();
 ensures n % 4u64 <= 3u64 by {
  have 0u64 <= n by normalize();
  apply(uint64_remainder_to_integer(n, 4u64)) using { 4u64 != 0u64; to_integer(4u64) != 0; };
  apply(integer_positive_divisor_remainder_upper(to_integer(n), 4)) using { 4 != 0; 0 < 4; };
  have to_integer(n % 4u64) <= to_integer(3u64) by { rewrite(to_integer(n % 4u64) == truncating_remainder(to_integer(n), to_integer(4u64))); assumption(); }
  assumption();
 }
}
