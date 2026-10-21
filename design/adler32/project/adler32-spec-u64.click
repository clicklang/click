import click::integer;
import click::machine_integer;

// The shared Adler-32 specification over a full-width length: lengths and
// indices are uint64, sums and weights are Integer, so subtracting a weight
// never wraps. It states the same theorems as adler32-spec.click, which reads
// lengths only up to INT32_MAX, with each signed bound replaced by the
// unsigned no-overflow condition. adler32-spec-bridge.click equates the two
// at every length both can state; the trials move to this file one stage at
// a time, after which the int32 specification and the _u64 suffix go away.

function adler_byte_sum_u64(bytes: uint8[], end: uint64) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer(bytes[k]) })
}
function adler_weighted_sum_u64(bytes: uint8[], end: uint64, weight_end: Integer) -> Integer {
 (0..end).fold(0, |acc, k| {
  acc + (weight_end - to_integer(k)) * to_integer(bytes[k])
 })
}

theorem adler_sum_empty_u64(bytes: uint8[], weight_end: Integer) {
 ensures adler_byte_sum_u64(bytes, 0u64) == 0 by { peel(adler_byte_sum_u64(bytes, 0u64)) using { 0u64 >= 0u64; }; simp(); }
 ensures adler_weighted_sum_u64(bytes, 0u64, weight_end) == 0 by { peel(adler_weighted_sum_u64(bytes, 0u64, weight_end)) using { 0u64 >= 0u64; }; simp(); }
}

theorem adler_sum_append_u64(bytes: uint8[], n: uint64) {
 requires 0u64 < n;
 ensures adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]) by {
  have 0u64 <= n - 1u64 by normalize();
  have n - 1u64 < 18446744073709551615u64 by arithmetic() using { 0u64 < n; };
  peel(adler_byte_sum_u64(bytes, n)) using { 0u64 <= n - 1u64; n - 1u64 < 18446744073709551615u64; };
  normalize();
 }
}

theorem adler_weighted_append_u64(bytes: uint8[], n: uint64, weight_end: Integer) {
 requires 0u64 < n;
 ensures adler_weighted_sum_u64(bytes, n, weight_end) == adler_weighted_sum_u64(bytes, n - 1u64, weight_end) + (weight_end - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]) by {
  have 0u64 <= n - 1u64 by normalize();
  have n - 1u64 < 18446744073709551615u64 by arithmetic() using { 0u64 < n; };
  peel(adler_weighted_sum_u64(bytes, n, weight_end)) using { 0u64 <= n - 1u64; n - 1u64 < 18446744073709551615u64; };
  normalize();
 }
}

theorem adler_weight_shift_u64(bytes: uint8[], n: uint64, w0: Integer, w1: Integer) {
 ensures adler_weighted_sum_u64(bytes, n, w1) - adler_weighted_sum_u64(bytes, n, w0) == (w1 - w0) * adler_byte_sum_u64(bytes, n) by {
  induct(n) as ih;
  if n <= 0u64 {
   have n == 0u64 by arithmetic() using { n <= 0u64; };
   rewrite(n == 0u64);
   apply(adler_sum_empty_u64(bytes, w1));
   apply(adler_sum_empty_u64(bytes, w0));
   rewrite(adler_weighted_sum_u64(bytes, 0u64, w1) == 0);
   rewrite(adler_weighted_sum_u64(bytes, 0u64, w0) == 0);
   rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
   arithmetic() using { };
  } else {
   have 0u64 < n by simp();
   have n - 1u64 < n by arithmetic() using { 0u64 < n; };
   apply(ih(n - 1u64)) using { n - 1u64 < n; };
   apply(adler_weighted_append_u64(bytes, n, w1)) using { 0u64 < n; };
   apply(adler_weighted_append_u64(bytes, n, w0)) using { 0u64 < n; };
   apply(adler_sum_append_u64(bytes, n)) using { 0u64 < n; };
   rewrite(adler_weighted_sum_u64(bytes, n, w1) == adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
   rewrite(adler_weighted_sum_u64(bytes, n, w0) == adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
   rewrite(adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
   have (adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) - (adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) == (adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0)) + (w1 - w0) * to_integer(bytes[n - 1u64]) by {
    arithmetic_certificate rules {
     integer_polynomial_identity bounds [] => (adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) - (adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) == (adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0)) + (w1 - w0) * to_integer(bytes[n - 1u64]);
     conclusion 0;
    }
   }
   rewrite((adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) - (adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) == (adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0)) + (w1 - w0) * to_integer(bytes[n - 1u64]));
   rewrite(adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0) == (w1 - w0) * adler_byte_sum_u64(bytes, n - 1u64));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (w1 - w0) * adler_byte_sum_u64(bytes, n - 1u64) + (w1 - w0) * to_integer(bytes[n - 1u64]) == (w1 - w0) * (adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
    conclusion 0;
   }
  }
 }
}

function adler_spec_a_u64(bytes: uint8[], length: uint64, a0: Integer) -> Integer {
 truncating_remainder(a0 + adler_byte_sum_u64(bytes, length), 65521)
}
function adler_spec_b_u64(bytes: uint8[], length: uint64, a0: Integer, b0: Integer) -> Integer {
 truncating_remainder(b0 + to_integer(length) * a0 + adler_weighted_sum_u64(bytes, length, to_integer(length)), 65521)
}

theorem adler_weighted_prefix_step_u64(bytes: uint8[], n: uint64) {
 requires 0u64 < n;
 ensures adler_weighted_sum_u64(bytes, n, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n) by {
  have 1u64 <= n by arithmetic() using { 0u64 < n; };
  apply(uint64_less_equal_to_integer(1u64, n)) using { 1u64 <= n; };
  apply(uint64_subtract_to_integer(n, 1u64)) using { to_integer(1u64) <= to_integer(n); };
  have to_integer(n) - to_integer(n - 1u64) == 1 by { arithmetic() using { to_integer(n - 1u64) == to_integer(n) - to_integer(1u64); }; }
  apply(adler_weight_shift_u64(bytes, n - 1u64, to_integer(n - 1u64), to_integer(n)));
  have adler_byte_sum_u64(bytes, n - 1u64) == (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64) by {
   rewrite(to_integer(n) - to_integer(n - 1u64) == 1);
   arithmetic() using { };
  }
  have adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n - 1u64) by {
   rewrite(adler_byte_sum_u64(bytes, n - 1u64) == (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64));
   arithmetic() using { adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) - adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) == (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64); to_integer(n) - to_integer(n - 1u64) == 1; };
  }
  apply(adler_weighted_append_u64(bytes, n, to_integer(n))) using { 0u64 < n; };
  apply(adler_sum_append_u64(bytes, n)) using { 0u64 < n; };
  rewrite(adler_weighted_sum_u64(bytes, n, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) + (to_integer(n) - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
  rewrite(adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n - 1u64));
  rewrite(to_integer(n) - to_integer(n - 1u64) == 1);
  rewrite(adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
  arithmetic() using { };
 }
}

theorem adler_byte_bounds_u64(value: uint8) {
 ensures 0 <= to_integer(value) by {
  arithmetic_certificate {
   negated_goal => to_integer(value) < 0;
   type_range => 0 <= to_integer(value);
   add 0, 1 => (to_integer(value) + 0) < (0 + to_integer(value));
   conclusion 2;
  }
 }
 ensures to_integer(value) <= 255 by {
  arithmetic_certificate {
   negated_goal => 255 < to_integer(value);
   type_range => to_integer(value) <= 255;
   add 0, 1 => (255 + to_integer(value)) < (to_integer(value) + 255);
   conclusion 2;
  }
 }
}

theorem adler_sum_nonnegative_u64(bytes: uint8[], n: uint64) {
 ensures 0 <= adler_byte_sum_u64(bytes, n) by {
  induct(n) as ih;
  if n <= 0u64 {
   have n == 0u64 by arithmetic() using { n <= 0u64; };
   rewrite(n == 0u64);
   apply(adler_sum_empty_u64(bytes, 0));
   rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
   arithmetic() using { };
  } else {
   have 0u64 < n by simp();
   have n - 1u64 < n by arithmetic() using { 0u64 < n; };
   apply(ih(n - 1u64)) using { n - 1u64 < n; };
   apply(adler_byte_bounds_u64(bytes[n - 1u64]));
   apply(adler_sum_append_u64(bytes, n)) using { 0u64 < n; };
   rewrite(adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
   arithmetic() using { 0 <= adler_byte_sum_u64(bytes, n - 1u64); 0 <= to_integer(bytes[n - 1u64]); };
  }
 }
}
theorem adler_weighted_nonnegative_u64(bytes: uint8[], n: uint64) {
 ensures 0 <= adler_weighted_sum_u64(bytes, n, to_integer(n)) by {
  induct(n) as ih;
  if n <= 0u64 {
   have n == 0u64 by arithmetic() using { n <= 0u64; };
   rewrite(n == 0u64);
   apply(adler_sum_empty_u64(bytes, to_integer(n)));
   rewrite(adler_weighted_sum_u64(bytes, 0u64, to_integer(n)) == 0);
   arithmetic() using { };
  } else {
   have 0u64 < n by simp();
   have n - 1u64 < n by arithmetic() using { 0u64 < n; };
   apply(ih(n - 1u64)) using { n - 1u64 < n; };
   apply(adler_sum_nonnegative_u64(bytes, n));
   apply(adler_weighted_prefix_step_u64(bytes, n)) using { 0u64 < n; };
   rewrite(adler_weighted_sum_u64(bytes, n, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n));
   arithmetic() using { 0 <= adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)); 0 <= adler_byte_sum_u64(bytes, n); };
  }
 }
}
theorem adler_residue_unique_u64(n: Integer, q: Integer, r: Integer) {
 requires 0 <= n;
 requires n == q * 65521 + r;
 requires 0 <= r;
 requires r <= 65520;
 ensures truncating_remainder(n, 65521) == r by {
  if q < 0 {
   have q <= -1 by { arithmetic() using { q < 0; }; }
   have n <= -1 by { arithmetic() using { n == q * 65521 + r; q <= -1; r <= 65520; }; }
   have not (0 <= n) by { arithmetic() using { n <= -1; }; }
   contradiction(0 <= n);
  } else {
   have 0 <= q by { arithmetic() using { not (q < 0); }; }
   have q * 65521 <= n by { arithmetic() using { n == q * 65521 + r; 0 <= r; }; }
   have n < (q + 1) * 65521 by { arithmetic() using { n == q * 65521 + r; r <= 65520; }; }
   have 0 < q + 1 by { arithmetic() using { 0 <= q; }; }
   apply(integer_positive_divisor_quotient_lower(n, 65521, q)) using { 65521 != 0; 1 <= 65521; q * 65521 <= n; };
   apply(integer_positive_divisor_quotient_strict_upper(n, 65521, q + 1)) using { 65521 != 0; 1 <= 65521; 0 < q + 1; n < (q + 1) * 65521; };
   have truncating_quotient(n, 65521) == q by { arithmetic() using { q <= truncating_quotient(n, 65521); truncating_quotient(n, 65521) < q + 1; }; }
   apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; };
   arithmetic() using { n == q * 65521 + r; n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); truncating_quotient(n, 65521) == q; };
  }
 }
}

theorem adler_residue_add_u64(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
  apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity(m, 65521)) using { 65521 != 0; };
  apply(integer_nonnegative_dividend_remainder(n, 65521)) using { 65521 != 0; 0 <= n; };
  apply(integer_nonnegative_dividend_remainder(m, 65521)) using { 65521 != 0; 0 <= m; };
  have 0 <= n + m by { arithmetic() using { 0 <= n; 0 <= m; }; }
  have 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521) by { arithmetic() using { 0 <= truncating_remainder(n, 65521); 0 <= truncating_remainder(m, 65521); }; }
  apply(integer_truncation_identity(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; };
  apply(integer_nonnegative_dividend_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521); };
  apply(integer_positive_divisor_remainder_upper(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 < 65521; };
  have n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
   arithmetic() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); truncating_remainder(n, 65521) + truncating_remainder(m, 65521) == truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521); };
  }
  apply(adler_residue_unique_u64(n + m, truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521), truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521))) using {
   0 <= n + m;
   n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   0 <= truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) <= 65520;
  };
  assumption();
 }
}

function adler_spec_checksum_u64(bytes: uint8[], length: uint64, a0: Integer, b0: Integer) -> Integer {
 65536 * adler_spec_b_u64(bytes, length, a0, b0) + adler_spec_a_u64(bytes, length, a0)
}

theorem adler_spec_a_canonical_u64(bytes: uint8[], n: uint64, a0: Integer) {
 requires 0 <= a0;
 ensures 0 <= adler_spec_a_u64(bytes, n, a0) and adler_spec_a_u64(bytes, n, a0) <= 65520 by {
  apply(adler_sum_nonnegative_u64(bytes, n));
  have 0 <= a0 + adler_byte_sum_u64(bytes, n) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, n); }; }
  apply(integer_nonnegative_dividend_remainder(a0 + adler_byte_sum_u64(bytes, n), 65521)) using { 65521 != 0; 0 <= a0 + adler_byte_sum_u64(bytes, n); };
  apply(integer_positive_divisor_remainder_upper(a0 + adler_byte_sum_u64(bytes, n), 65521)) using { 65521 != 0; 0 < 65521; };
  unfold(adler_spec_a_u64(bytes, n, a0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_b_canonical_u64(bytes: uint8[], n: uint64, a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_b_u64(bytes, n, a0, b0) and adler_spec_b_u64(bytes, n, a0, b0) <= 65520 by {
  apply(adler_weighted_nonnegative_u64(bytes, n));
  apply(uint64_to_integer_bounds(n));
  have 0 <= to_integer(n) * a0 by {
   arithmetic_certificate rules {
    premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
    premise 1: to_integer(n) <= 18446744073709551615 => to_integer(n) <= 18446744073709551615;
    premise 2: 0 <= a0 => 0 <= a0;
    premise 3: a0 <= 65520 => a0 <= 65520;
    integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(n) * a0;
    conclusion 0;
   }
  }
  have 0 <= b0 + to_integer(n) * a0 by { arithmetic() using { 0 <= b0; 0 <= to_integer(n) * a0; }; }
  have 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)) by { arithmetic() using { 0 <= b0 + to_integer(n) * a0; 0 <= adler_weighted_sum_u64(bytes, n, to_integer(n)); }; }
  apply(integer_nonnegative_dividend_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521)) using { 65521 != 0; 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)); };
  apply(integer_positive_divisor_remainder_upper(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521)) using { 65521 != 0; 0 < 65521; };
  unfold(adler_spec_b_u64(bytes, n, a0, b0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_packing_bounds_u64(bytes: uint8[], n: uint64, a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_checksum_u64(bytes, n, a0, b0) and adler_spec_checksum_u64(bytes, n, a0, b0) <= 4293984240 by {
  apply(adler_spec_a_canonical_u64(bytes, n, a0)) using { 0 <= a0; };
  apply(adler_spec_b_canonical_u64(bytes, n, a0, b0)) using { 0 <= a0; a0 <= 65520; 0 <= b0; };
  unfold(adler_spec_checksum_u64(bytes, n, a0, b0));
  both {
   arithmetic() using { 0 <= adler_spec_b_u64(bytes, n, a0, b0); 0 <= adler_spec_a_u64(bytes, n, a0); };
  } and {
   arithmetic() using { adler_spec_b_u64(bytes, n, a0, b0) <= 65520; adler_spec_a_u64(bytes, n, a0) <= 65520; };
  }
 }
}

theorem adler_spec_empty_u64(bytes: uint8[], a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 requires b0 <= 65520;
 ensures adler_spec_a_u64(bytes, 0u64, a0) == a0 by {
  apply(adler_sum_empty_u64(bytes, 0));
  have a0 == 0 * 65521 + a0 by { arithmetic() using {}; }
  apply(adler_residue_unique_u64(a0, 0, a0)) using { 0 <= a0; a0 == 0 * 65521 + a0; 0 <= a0; a0 <= 65520; };
  unfold(adler_spec_a_u64(bytes, 0u64, a0));
  rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
  simp() using { truncating_remainder(a0, 65521) == a0; };
 }
 ensures adler_spec_b_u64(bytes, 0u64, a0, b0) == b0 by {
  apply(adler_sum_empty_u64(bytes, to_integer(0u64)));
  have b0 == 0 * 65521 + b0 by { arithmetic() using {}; }
  apply(adler_residue_unique_u64(b0, 0, b0)) using { 0 <= b0; b0 == 0 * 65521 + b0; 0 <= b0; b0 <= 65520; };
  unfold(adler_spec_b_u64(bytes, 0u64, a0, b0));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, to_integer(0u64)) == 0);
  simp() using { truncating_remainder(b0, 65521) == b0; };
 }
}

theorem adler_byte_observation_same_index_u64(bytes: uint8[], i: uint64, j: uint64) {
 requires i == j;
 ensures to_integer(bytes[i]) == to_integer(bytes[j]) by { rewrite(i == j); normalize(); }
}
theorem adler_sum_append_four_u64(bytes: uint8[], n: uint64) {
 requires n <= 18446744073709551611u64;
 ensures adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) + to_integer(bytes[n + 1u64]) + to_integer(bytes[n + 2u64]) + to_integer(bytes[n + 3u64]) by {
  have 0u64 < n + 1u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 1u64) - 1u64 == n by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 1u64)) using { 0u64 < n + 1u64; };
  have adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) by { simp() using { adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, (n + 1u64) - 1u64) + to_integer(bytes[(n + 1u64) - 1u64]); (n + 1u64) - 1u64 == n; }; }
  have 0u64 < n + 2u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 2u64) - 1u64 == n + 1u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 2u64)) using { 0u64 < n + 2u64; };
  have n + 1u64 == (n + 2u64) - 1u64 by { simp() using { (n + 2u64) - 1u64 == n + 1u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 1u64, (n + 2u64) - 1u64)) using { n + 1u64 == (n + 2u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]) by { rewrite(n + 1u64 == (n + 2u64) - 1u64); rewrite(to_integer(bytes[n + 1u64]) == to_integer(bytes[(n + 2u64) - 1u64])); assumption(); }
  have 0u64 < n + 3u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 3u64) - 1u64 == n + 2u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 3u64)) using { 0u64 < n + 3u64; };
  have n + 2u64 == (n + 3u64) - 1u64 by { simp() using { (n + 3u64) - 1u64 == n + 2u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 2u64, (n + 3u64) - 1u64)) using { n + 2u64 == (n + 3u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]) by { rewrite(n + 2u64 == (n + 3u64) - 1u64); rewrite(to_integer(bytes[n + 2u64]) == to_integer(bytes[(n + 3u64) - 1u64])); assumption(); }
  have 0u64 < n + 4u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 4u64) - 1u64 == n + 3u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 4u64)) using { 0u64 < n + 4u64; };
  have n + 3u64 == (n + 4u64) - 1u64 by { simp() using { (n + 4u64) - 1u64 == n + 3u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 3u64, (n + 4u64) - 1u64)) using { n + 3u64 == (n + 4u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]) by { rewrite(n + 3u64 == (n + 4u64) - 1u64); rewrite(to_integer(bytes[n + 3u64]) == to_integer(bytes[(n + 4u64) - 1u64])); assumption(); }
  rewrite(adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]));
  arithmetic() using {};
 }
}

theorem adler_weighted_append_four_u64(bytes: uint8[], n: uint64) {
 requires n <= 18446744073709551611u64;
 ensures adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)) == adler_weighted_sum_u64(bytes, n, to_integer(n)) + 4 * adler_byte_sum_u64(bytes, n) + 4 * to_integer(bytes[n]) + 3 * to_integer(bytes[n + 1u64]) + 2 * to_integer(bytes[n + 2u64]) + to_integer(bytes[n + 3u64]) by {
  have 0u64 < n + 1u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 1u64) - 1u64 == n by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 1u64)) using { 0u64 < n + 1u64; };
  have adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) by { simp() using { adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, (n + 1u64) - 1u64) + to_integer(bytes[(n + 1u64) - 1u64]); (n + 1u64) - 1u64 == n; }; }
  have 0u64 < n + 2u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 2u64) - 1u64 == n + 1u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 2u64)) using { 0u64 < n + 2u64; };
  have n + 1u64 == (n + 2u64) - 1u64 by { simp() using { (n + 2u64) - 1u64 == n + 1u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 1u64, (n + 2u64) - 1u64)) using { n + 1u64 == (n + 2u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]) by { rewrite(n + 1u64 == (n + 2u64) - 1u64); rewrite(to_integer(bytes[n + 1u64]) == to_integer(bytes[(n + 2u64) - 1u64])); assumption(); }
  have 0u64 < n + 3u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 3u64) - 1u64 == n + 2u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 3u64)) using { 0u64 < n + 3u64; };
  have n + 2u64 == (n + 3u64) - 1u64 by { simp() using { (n + 3u64) - 1u64 == n + 2u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 2u64, (n + 3u64) - 1u64)) using { n + 2u64 == (n + 3u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]) by { rewrite(n + 2u64 == (n + 3u64) - 1u64); rewrite(to_integer(bytes[n + 2u64]) == to_integer(bytes[(n + 3u64) - 1u64])); assumption(); }
  have 0u64 < n + 4u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  have (n + 4u64) - 1u64 == n + 3u64 by { arithmetic() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 4u64)) using { 0u64 < n + 4u64; };
  have n + 3u64 == (n + 4u64) - 1u64 by { simp() using { (n + 4u64) - 1u64 == n + 3u64; }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 3u64, (n + 4u64) - 1u64)) using { n + 3u64 == (n + 4u64) - 1u64; };
  have adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]) by { rewrite(n + 3u64 == (n + 4u64) - 1u64); rewrite(to_integer(bytes[n + 3u64]) == to_integer(bytes[(n + 4u64) - 1u64])); assumption(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 1u64)) using { 0u64 < n + 1u64; };
  have adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) == adler_weighted_sum_u64(bytes, n, to_integer(n)) + adler_byte_sum_u64(bytes, n + 1u64) by { simp() using { adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) == adler_weighted_sum_u64(bytes, (n + 1u64) - 1u64, to_integer((n + 1u64) - 1u64)) + adler_byte_sum_u64(bytes, n + 1u64); (n + 1u64) - 1u64 == n; }; }
  apply(adler_weighted_prefix_step_u64(bytes, n + 2u64)) using { 0u64 < n + 2u64; };
  have adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) == adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) + adler_byte_sum_u64(bytes, n + 2u64) by { rewrite(n + 1u64 == (n + 2u64) - 1u64); assumption(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 3u64)) using { 0u64 < n + 3u64; };
  have adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) == adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) + adler_byte_sum_u64(bytes, n + 3u64) by { rewrite(n + 2u64 == (n + 3u64) - 1u64); assumption(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 4u64)) using { 0u64 < n + 4u64; };
  have adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)) == adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) + adler_byte_sum_u64(bytes, n + 4u64) by { rewrite(n + 3u64 == (n + 4u64) - 1u64); assumption(); }
  rewrite(adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)) == adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) + adler_byte_sum_u64(bytes, n + 4u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) == adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) + adler_byte_sum_u64(bytes, n + 3u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) == adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) + adler_byte_sum_u64(bytes, n + 2u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) == adler_weighted_sum_u64(bytes, n, to_integer(n)) + adler_byte_sum_u64(bytes, n + 1u64));
  rewrite(adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]));
  arithmetic() using {};
 }
}// A signed quotient difference can witness congruence even when either
// representative is smaller. Both dividend interpretations remain nonnegative.
theorem adler_residue_congruent_u64(n: Integer, m: Integer, q: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 requires n == m + 65521 * q;
 ensures truncating_remainder(n, 65521) == truncating_remainder(m, 65521) by {
  apply(integer_truncation_identity(m, 65521)) using { 65521 != 0; };
  apply(integer_nonnegative_dividend_remainder(m, 65521)) using { 65521 != 0; 0 <= m; };
  apply(integer_positive_divisor_remainder_upper(m, 65521)) using { 65521 != 0; 0 < 65521; };
  have n == (truncating_quotient(m, 65521) + q) * 65521 + truncating_remainder(m, 65521) by {
   arithmetic() using { n == m + 65521 * q; m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); };
  }
  apply(adler_residue_unique_u64(n, truncating_quotient(m, 65521) + q, truncating_remainder(m, 65521))) using {
   0 <= n;
   n == (truncating_quotient(m, 65521) + q) * 65521 + truncating_remainder(m, 65521);
   0 <= truncating_remainder(m, 65521);
   truncating_remainder(m, 65521) <= 65520;
  };
  assumption();
 }
}

theorem adler_spec_one_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 1u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 1));
  apply(adler_sum_append_u64(bytes, 1u64));
  unfold(adler_spec_a_u64(bytes, 1u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 1u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]));
  rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
  simp();
 }
 ensures adler_spec_b_u64(bytes, 1u64, 1, 0) == truncating_remainder(1 + to_integer(bytes[0u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 1));
  apply(adler_weighted_append_u64(bytes, 1u64, 1));
  unfold(adler_spec_b_u64(bytes, 1u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 1u64, 1) == adler_weighted_sum_u64(bytes, 0u64, 1) + to_integer(bytes[0u64]));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, 1) == 0);
  simp();
 }
}

theorem adler_byte_offset_association_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures to_integer((bytes + prefix)[suffix]) == to_integer(bytes[prefix + suffix]) by {
  apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
  have (bytes + prefix) + suffix == bytes + (prefix + suffix) by { normalize() using { to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix); }; }
  rewrite((bytes + prefix) + suffix == bytes + (prefix + suffix));
  simp();
 }
}

theorem adler_sum_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures adler_byte_sum_u64(bytes, prefix + suffix) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix) by {
  induct(suffix) as ih;
  if suffix <= 0u64 {
   have suffix == 0u64 by arithmetic() using { suffix <= 0u64; };
   have prefix + suffix == prefix by { rewrite(suffix == 0u64); normalize(); }
   apply(adler_sum_empty_u64(bytes + prefix, 0));
   have adler_byte_sum_u64(bytes + prefix, suffix) == 0 by { rewrite(suffix == 0u64); assumption(); }
   rewrite(prefix + suffix == prefix);
   arithmetic() using { adler_byte_sum_u64(bytes + prefix, suffix) == 0; };
  } else {
   have 0u64 < suffix by simp();
   have suffix - 1u64 < suffix by arithmetic() using { 0u64 < suffix; };
   have 1u64 <= suffix by arithmetic() using { 0u64 < suffix; };
   apply(uint64_less_equal_to_integer(1u64, suffix)) using { 1u64 <= suffix; };
   apply(uint64_subtract_to_integer(suffix, 1u64)) using { to_integer(1u64) <= to_integer(suffix); };
   have to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615 by arithmetic() using {
    to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(ih(suffix - 1u64)) using { suffix - 1u64 < suffix; to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
   apply(uint64_add_to_integer(prefix, suffix - 1u64)) using { to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   apply(uint64_to_integer_bounds(prefix));
   have to_integer(0u64) < to_integer(prefix + suffix) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   apply(uint64_to_integer_less_than_implies_less_than(0u64, prefix + suffix)) using { to_integer(0u64) < to_integer(prefix + suffix); };
   have 0u64 < prefix + suffix by assumption();
   have to_integer(1u64) <= to_integer(prefix + suffix) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   apply(uint64_subtract_to_integer(prefix + suffix, 1u64)) using { to_integer(1u64) <= to_integer(prefix + suffix); };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(uint64_to_integer_equal_implies_equal((prefix + suffix) - 1u64, prefix + (suffix - 1u64))) using { to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)); };
   have (prefix + suffix) - 1u64 == prefix + (suffix - 1u64) by assumption();
   apply(adler_sum_append_u64(bytes, prefix + suffix)) using { 0u64 < prefix + suffix; };
   apply(adler_sum_append_u64(bytes + prefix, suffix)) using { 0u64 < suffix; };
   apply(adler_byte_offset_association_u64(bytes, prefix, suffix - 1u64)) using { to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   have adler_byte_sum_u64(bytes, (prefix + suffix) - 1u64) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix - 1u64) by {
    rewrite((prefix + suffix) - 1u64 == prefix + (suffix - 1u64)); assumption();
   }
   have to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite((prefix + suffix) - 1u64 == prefix + (suffix - 1u64)); arithmetic() using { to_integer((bytes + prefix)[suffix - 1u64]) == to_integer(bytes[prefix + (suffix - 1u64)]); };
   }
   arithmetic() using {
    adler_byte_sum_u64(bytes, prefix + suffix) == adler_byte_sum_u64(bytes, (prefix + suffix) - 1u64) + to_integer(bytes[(prefix + suffix) - 1u64]);
    adler_byte_sum_u64(bytes + prefix, suffix) == adler_byte_sum_u64(bytes + prefix, suffix - 1u64) + to_integer((bytes + prefix)[suffix - 1u64]);
    adler_byte_sum_u64(bytes, (prefix + suffix) - 1u64) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix - 1u64);
    to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]);
   };
  }
 }
}

theorem adler_weighted_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64, weight_end: Integer) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures adler_weighted_sum_u64(bytes, prefix + suffix, weight_end) == adler_weighted_sum_u64(bytes, prefix, weight_end) + adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)) by {
  induct(suffix) as ih;
  if suffix <= 0u64 {
   have suffix == 0u64 by arithmetic() using { suffix <= 0u64; };
   have prefix + suffix == prefix by { rewrite(suffix == 0u64); normalize(); }
   apply(adler_sum_empty_u64(bytes + prefix, weight_end - to_integer(prefix)));
   have adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)) == 0 by { rewrite(suffix == 0u64); assumption(); }
   rewrite(prefix + suffix == prefix);
   arithmetic() using { adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)) == 0; };
  } else {
   have 0u64 < suffix by simp();
   have suffix - 1u64 < suffix by arithmetic() using { 0u64 < suffix; };
   have 1u64 <= suffix by arithmetic() using { 0u64 < suffix; };
   apply(uint64_less_equal_to_integer(1u64, suffix)) using { 1u64 <= suffix; };
   apply(uint64_subtract_to_integer(suffix, 1u64)) using { to_integer(1u64) <= to_integer(suffix); };
   have to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615 by arithmetic() using {
    to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(ih(suffix - 1u64)) using { suffix - 1u64 < suffix; to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
   apply(uint64_add_to_integer(prefix, suffix - 1u64)) using { to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   apply(uint64_to_integer_bounds(prefix));
   have to_integer(0u64) < to_integer(prefix + suffix) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   apply(uint64_to_integer_less_than_implies_less_than(0u64, prefix + suffix)) using { to_integer(0u64) < to_integer(prefix + suffix); };
   have 0u64 < prefix + suffix by assumption();
   have to_integer(1u64) <= to_integer(prefix + suffix) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   apply(uint64_subtract_to_integer(prefix + suffix, 1u64)) using { to_integer(1u64) <= to_integer(prefix + suffix); };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(uint64_to_integer_equal_implies_equal((prefix + suffix) - 1u64, prefix + (suffix - 1u64))) using { to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)); };
   have (prefix + suffix) - 1u64 == prefix + (suffix - 1u64) by assumption();
   apply(adler_weighted_append_u64(bytes, prefix + suffix, weight_end)) using { 0u64 < prefix + suffix; };
   apply(adler_weighted_append_u64(bytes + prefix, suffix, weight_end - to_integer(prefix))) using { 0u64 < suffix; };
   apply(adler_byte_offset_association_u64(bytes, prefix, suffix - 1u64)) using { to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615; };
   have adler_weighted_sum_u64(bytes, (prefix + suffix) - 1u64, weight_end) == adler_weighted_sum_u64(bytes, prefix, weight_end) + adler_weighted_sum_u64(bytes + prefix, suffix - 1u64, weight_end - to_integer(prefix)) by {
    rewrite((prefix + suffix) - 1u64 == prefix + (suffix - 1u64)); assumption();
   }
   have to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite((prefix + suffix) - 1u64 == prefix + (suffix - 1u64)); arithmetic() using { to_integer((bytes + prefix)[suffix - 1u64]) == to_integer(bytes[prefix + (suffix - 1u64)]); };
   }
   have weight_end - to_integer((prefix + suffix) - 1u64) == (weight_end - to_integer(prefix)) - to_integer(suffix - 1u64) by arithmetic() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   have (weight_end - to_integer((prefix + suffix) - 1u64)) * to_integer(bytes[(prefix + suffix) - 1u64]) == ((weight_end - to_integer(prefix)) - to_integer(suffix - 1u64)) * to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite(weight_end - to_integer((prefix + suffix) - 1u64) == (weight_end - to_integer(prefix)) - to_integer(suffix - 1u64));
    rewrite(to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]));
    simp();
   }
   arithmetic() using {
    adler_weighted_sum_u64(bytes, prefix + suffix, weight_end) == adler_weighted_sum_u64(bytes, (prefix + suffix) - 1u64, weight_end) + (weight_end - to_integer((prefix + suffix) - 1u64)) * to_integer(bytes[(prefix + suffix) - 1u64]);
    adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)) == adler_weighted_sum_u64(bytes + prefix, suffix - 1u64, weight_end - to_integer(prefix)) + ((weight_end - to_integer(prefix)) - to_integer(suffix - 1u64)) * to_integer((bytes + prefix)[suffix - 1u64]);
    adler_weighted_sum_u64(bytes, (prefix + suffix) - 1u64, weight_end) == adler_weighted_sum_u64(bytes, prefix, weight_end) + adler_weighted_sum_u64(bytes + prefix, suffix - 1u64, weight_end - to_integer(prefix));
    (weight_end - to_integer((prefix + suffix) - 1u64)) * to_integer(bytes[(prefix + suffix) - 1u64]) == ((weight_end - to_integer(prefix)) - to_integer(suffix - 1u64)) * to_integer((bytes + prefix)[suffix - 1u64]);
   };
  }
 }
}
theorem adler_residue_add_left_u64(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + m, 65521) by {
  apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; };
  apply(integer_nonnegative_dividend_remainder(n, 65521)) using { 65521 != 0; 0 <= n; };
  have 0 <= n + m by { arithmetic() using { 0 <= n; 0 <= m; }; }
  have 0 <= truncating_remainder(n, 65521) + m by { arithmetic() using { 0 <= truncating_remainder(n, 65521); 0 <= m; }; }
  have n + m == (truncating_remainder(n, 65521) + m) + 65521 * truncating_quotient(n, 65521) by { arithmetic() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); }; }
  apply(adler_residue_congruent_u64(n + m, truncating_remainder(n, 65521) + m, truncating_quotient(n, 65521)));
  assumption();
 }
}

theorem adler_spec_a_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64, a0: Integer) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 requires 0 <= a0;
 ensures adler_spec_a_u64(bytes, prefix + suffix, a0) == adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)) by {
  apply(adler_sum_concat_u64(bytes, prefix, suffix));
  apply(adler_sum_nonnegative_u64(bytes, prefix));
  apply(adler_sum_nonnegative_u64(bytes + prefix, suffix));
  have 0 <= a0 + adler_byte_sum_u64(bytes, prefix) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, prefix); }; }
  apply(adler_residue_add_left_u64(a0 + adler_byte_sum_u64(bytes, prefix), adler_byte_sum_u64(bytes + prefix, suffix)));
  unfold(adler_spec_a_u64(bytes, prefix + suffix, a0));
  unfold(adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)));
  unfold(adler_spec_a_u64(bytes, prefix, a0));
  rewrite(adler_byte_sum_u64(bytes, prefix + suffix) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix));
  have a0 + (adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix)) == (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_byte_sum_u64(bytes + prefix, suffix) by { arithmetic() using {}; }
  rewrite(a0 + (adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix)) == (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_byte_sum_u64(bytes + prefix, suffix));
  assumption();
 }
}

theorem adler_sum_upper_u64(bytes: uint8[], n: uint64) {
 ensures adler_byte_sum_u64(bytes, n) <= 255 * to_integer(n) by {
  induct(n) as ih;
  if n <= 0u64 {
   have n == 0u64 by arithmetic() using { n <= 0u64; };
   apply(adler_sum_empty_u64(bytes, 0));
   rewrite(n == 0u64);
   arithmetic() using { adler_byte_sum_u64(bytes, 0u64) == 0; };
  } else {
   have 0u64 < n by simp();
   have n - 1u64 < n by arithmetic() using { 0u64 < n; };
   apply(ih(n - 1u64)) using { n - 1u64 < n; };
   apply(adler_sum_append_u64(bytes, n)) using { 0u64 < n; };
   apply(adler_byte_bounds_u64(bytes[n - 1u64]));
   have 1u64 <= n by arithmetic() using { 0u64 < n; };
   apply(uint64_less_equal_to_integer(1u64, n)) using { 1u64 <= n; };
   apply(uint64_subtract_to_integer(n, 1u64)) using { to_integer(1u64) <= to_integer(n); };
   arithmetic() using {
    adler_byte_sum_u64(bytes, n - 1u64) <= 255 * to_integer(n - 1u64);
    adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]);
    to_integer(bytes[n - 1u64]) <= 255;
    to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
   };
  }
 }
}
theorem adler_seed_polynomial_u64(x: Integer, y: Integer, k: Integer, z: Integer, qa: Integer, ra: Integer, qb: Integer, rb: Integer) {
 requires x == qa * 65521 + ra;
 requires y == qb * 65521 + rb;
 ensures y + k * x + z == (rb + k * ra + z) + 65521 * (qb + k * qa) by {
  rewrite(y == qb * 65521 + rb);
  rewrite(x == qa * 65521 + ra);
  arithmetic_certificate rules {
   integer_polynomial_identity bounds [] => (qb * 65521 + rb) + k * (qa * 65521 + ra) + z == (rb + k * ra + z) + 65521 * (qb + k * qa); conclusion 0;
  }
 }
}
theorem adler_residue_seed_update_u64(x: Integer, y: Integer, k: Integer, z: Integer) {
 requires 0 <= x;
 requires x <= 4703919738795935727345;
 requires 0 <= y;
 requires 0 <= k;
 requires k <= 18446744073709551615;
 requires 0 <= z;
 ensures truncating_remainder(y + k * x + z, 65521) == truncating_remainder(truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, 65521) by {
  apply(integer_truncation_identity(x, 65521)) using { 65521 != 0; };
  apply(integer_truncation_identity(y, 65521)) using { 65521 != 0; };
  apply(integer_nonnegative_dividend_remainder(x, 65521)) using { 65521 != 0; 0 <= x; };
  apply(integer_nonnegative_dividend_remainder(y, 65521)) using { 65521 != 0; 0 <= y; };
  apply(integer_positive_divisor_remainder_upper(x, 65521)) using { 65521 != 0; 0 < 65521; };
  have 0 <= k * x by { arithmetic_certificate rules {
   premise 0: 0 <= k => 0 <= k;
   premise 1: k <= 18446744073709551615 => k <= 18446744073709551615;
   premise 2: 0 <= x => 0 <= x;
   premise 3: x <= 4703919738795935727345 => x <= 4703919738795935727345;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= k * x; conclusion 0;
  } }
  have 0 <= k * truncating_remainder(x, 65521) by { arithmetic_certificate rules {
   premise 0: 0 <= k => 0 <= k;
   premise 1: k <= 18446744073709551615 => k <= 18446744073709551615;
   premise 2: 0 <= truncating_remainder(x, 65521) => 0 <= truncating_remainder(x, 65521);
   premise 3: truncating_remainder(x, 65521) <= 65520 => truncating_remainder(x, 65521) <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= k * truncating_remainder(x, 65521); conclusion 0;
  } }
  have 0 <= y + k * x + z by { arithmetic_certificate {
   premise 0: 0 <= y => 0 <= y;
   premise 1: 0 <= k * x => 0 <= k * x;
   premise 2: 0 <= z => 0 <= z;
   add 0, 1 => 0 <= y + k * x;
   add 3, 2 => 0 <= y + k * x + z; conclusion 4;
  } }
  have 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z by { arithmetic_certificate {
   premise 0: 0 <= truncating_remainder(y, 65521) => 0 <= truncating_remainder(y, 65521);
   premise 1: 0 <= k * truncating_remainder(x, 65521) => 0 <= k * truncating_remainder(x, 65521);
   premise 2: 0 <= z => 0 <= z;
   add 0, 1 => 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521);
   add 3, 2 => 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z; conclusion 4;
  } }
  apply(adler_seed_polynomial_u64(x, y, k, z, truncating_quotient(x, 65521), truncating_remainder(x, 65521), truncating_quotient(y, 65521), truncating_remainder(y, 65521)));
  apply(adler_residue_congruent_u64(y + k * x + z, truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, truncating_quotient(y, 65521) + k * truncating_quotient(x, 65521)));
  assumption();
 }
}

theorem adler_concat_index_partition_u64(prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures defined((prefix + suffix) - prefix) and (prefix + suffix) - prefix == suffix by {
  apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
  apply(uint64_to_integer_bounds(suffix));
  have to_integer(prefix) <= to_integer(prefix + suffix) by arithmetic() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   0 <= to_integer(suffix);
  };
  apply(uint64_subtract_to_integer(prefix + suffix, prefix)) using { to_integer(prefix) <= to_integer(prefix + suffix); };
  have to_integer((prefix + suffix) - prefix) == to_integer(suffix) by arithmetic() using {
   to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  };
  apply(uint64_to_integer_equal_implies_equal((prefix + suffix) - prefix, suffix)) using { to_integer((prefix + suffix) - prefix) == to_integer(suffix); };
  both { normalize(); } and { assumption(); }
 }
}

theorem adler_weighted_prefix_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)) by {
  apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
  have to_integer(prefix + suffix) - to_integer(prefix) == to_integer(suffix) by arithmetic() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  };
  apply(adler_weighted_concat_u64(bytes, prefix, suffix, to_integer(prefix + suffix))) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
  have adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)) by {
   rewrite(to_integer(suffix) == to_integer(prefix + suffix) - to_integer(prefix));
   assumption();
  }
  apply(adler_weight_shift_u64(bytes, prefix, to_integer(prefix), to_integer(prefix + suffix)));
  have adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) - adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) == to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) by {
   rewrite(to_integer(suffix) == to_integer(prefix + suffix) - to_integer(prefix));
   assumption();
  }
  arithmetic() using {
   adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix));
   adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) - adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) == to_integer(suffix) * adler_byte_sum_u64(bytes, prefix);
  };
 }
}
theorem adler_join_seed_polynomial_u64(a0: Integer, b0: Integer, p: Integer, s: Integer, sp: Integer, wp: Integer, wt: Integer) {
 ensures b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt by {
  arithmetic_certificate rules {
   integer_polynomial_identity bounds [] => b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt; conclusion 0;
  }
 }
}

theorem adler_spec_b_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64, a0: Integer, b0: Integer) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_b_u64(bytes, prefix + suffix, a0, b0) == adler_spec_b_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)) by {
  apply(adler_weighted_prefix_concat_u64(bytes, prefix, suffix));
  apply(adler_sum_nonnegative_u64(bytes, prefix));
  apply(adler_sum_upper_u64(bytes, prefix));
  apply(adler_weighted_nonnegative_u64(bytes, prefix));
  apply(adler_weighted_nonnegative_u64(bytes + prefix, suffix));
  apply(uint64_to_integer_bounds(prefix));
  apply(uint64_to_integer_bounds(suffix));
  have 0 <= to_integer(prefix) * a0 by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(prefix) => 0 <= to_integer(prefix);
   premise 1: to_integer(prefix) <= 18446744073709551615 => to_integer(prefix) <= 18446744073709551615;
   premise 2: 0 <= a0 => 0 <= a0;
   premise 3: a0 <= 65520 => a0 <= 65520;
   integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(prefix) * a0; conclusion 0;
  } }
  have 0 <= a0 + adler_byte_sum_u64(bytes, prefix) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, prefix); }; }
  have 255 * to_integer(prefix) <= 4703919738795935661825 by { arithmetic_certificate {
   premise 0: to_integer(prefix) <= 18446744073709551615 => to_integer(prefix) <= 18446744073709551615;
   scale 0 by 255 => 255 * to_integer(prefix) <= 255 * 18446744073709551615; conclusion 1;
  } }
  have adler_byte_sum_u64(bytes, prefix) <= 4703919738795935661825 by { arithmetic() using {
   adler_byte_sum_u64(bytes, prefix) <= 255 * to_integer(prefix);
   255 * to_integer(prefix) <= 4703919738795935661825;
  }; }
  have a0 + adler_byte_sum_u64(bytes, prefix) <= 4703919738795935727345 by { arithmetic() using {
   a0 <= 65520; adler_byte_sum_u64(bytes, prefix) <= 4703919738795935661825;
  }; }
  have 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) by { arithmetic_certificate {
   premise 0: 0 <= b0 => 0 <= b0;
   premise 1: 0 <= to_integer(prefix) * a0 => 0 <= to_integer(prefix) * a0;
   premise 2: 0 <= adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) => 0 <= adler_weighted_sum_u64(bytes, prefix, to_integer(prefix));
   add 0, 1 => 0 <= b0 + to_integer(prefix) * a0;
   add 3, 2 => 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)); conclusion 4;
  } }
  apply(adler_residue_seed_update_u64(a0 + adler_byte_sum_u64(bytes, prefix), b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)), to_integer(suffix), adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))));
  apply(uint64_add_to_integer(prefix, suffix)) using { to_integer(prefix) + to_integer(suffix) <= 18446744073709551615; };
  apply(adler_join_seed_polynomial_u64(a0, b0, to_integer(prefix), to_integer(suffix), adler_byte_sum_u64(bytes, prefix), adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)), adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))));
  unfold(adler_spec_b_u64(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_b_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)));
  unfold(adler_spec_a_u64(bytes, prefix, a0));
  unfold(adler_spec_b_u64(bytes, prefix, a0, b0));
  rewrite(adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)));
  rewrite(to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix));
  rewrite(b0 + (to_integer(prefix) + to_integer(suffix)) * a0 + (adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))) == (b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix))) + to_integer(suffix) * (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)));
  assumption();
 }
}

theorem adler_spec_checksum_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64, a0: Integer, b0: Integer) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_checksum_u64(bytes, prefix + suffix, a0, b0) == adler_spec_checksum_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)) by {
  apply(adler_spec_a_concat_u64(bytes, prefix, suffix, a0));
  apply(adler_spec_b_concat_u64(bytes, prefix, suffix, a0, b0));
  unfold(adler_spec_checksum_u64(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_checksum_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)));
  rewrite(adler_spec_a_u64(bytes, prefix + suffix, a0) == adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)));
  rewrite(adler_spec_b_u64(bytes, prefix + suffix, a0, b0) == adler_spec_b_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)));
  simp();
 }
}

theorem adler_spec_four_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 4u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 0));
  apply(adler_sum_append_four_u64(bytes, 0u64));
  have 1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]) by { arithmetic() using {}; }
  unfold(adler_spec_a_u64(bytes, 4u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 4u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]));
  rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
  rewrite(1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])); simp();
 }
 ensures adler_spec_b_u64(bytes, 4u64, 1, 0) == truncating_remainder(4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 0));
  apply(adler_weighted_append_four_u64(bytes, 0u64));
  have 4 + (4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]) by { arithmetic() using {}; }
  unfold(adler_spec_b_u64(bytes, 4u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 4u64, 4) == adler_weighted_sum_u64(bytes, 0u64, 0) + 4 * adler_byte_sum_u64(bytes, 0u64) + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, 0) == 0);
  rewrite(adler_byte_sum_u64(bytes, 0u64) == 0);
  rewrite(4 + (4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])); simp();
 }
}

theorem adler_spec_two_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 2u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 2));
  apply(adler_sum_append_u64(bytes, 1u64));
  apply(adler_sum_append_u64(bytes, 2u64));
  have adler_byte_sum_u64(bytes, 2u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { arithmetic() using { adler_byte_sum_u64(bytes, 0u64) == 0; adler_byte_sum_u64(bytes, 1u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]); adler_byte_sum_u64(bytes, 2u64) == adler_byte_sum_u64(bytes, 1u64) + to_integer(bytes[1u64]); }; }
  have 1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { arithmetic() using {}; }
  unfold(adler_spec_a_u64(bytes, 2u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 2u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  rewrite(1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  simp();
 }
 ensures adler_spec_b_u64(bytes, 2u64, 1, 0) == truncating_remainder(2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 2));
  apply(adler_weighted_append_u64(bytes, 1u64, 2));
  apply(adler_weighted_append_u64(bytes, 2u64, 2));
  have adler_weighted_sum_u64(bytes, 2u64, 2) == 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { arithmetic() using { adler_weighted_sum_u64(bytes, 0u64, 2) == 0; adler_weighted_sum_u64(bytes, 1u64, 2) == adler_weighted_sum_u64(bytes, 0u64, 2) + 2 * to_integer(bytes[0u64]); adler_weighted_sum_u64(bytes, 2u64, 2) == adler_weighted_sum_u64(bytes, 1u64, 2) + 1 * to_integer(bytes[1u64]); }; }
  have 2 + (2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { arithmetic() using {}; }
  unfold(adler_spec_b_u64(bytes, 2u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 2u64, 2) == 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  rewrite(2 + (2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  simp();
 }
}

theorem adler_spec_three_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 3u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 3));
  apply(adler_sum_append_u64(bytes, 1u64));
  apply(adler_sum_append_u64(bytes, 2u64));
  apply(adler_sum_append_u64(bytes, 3u64));
  have adler_byte_sum_u64(bytes, 3u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { arithmetic() using { adler_byte_sum_u64(bytes, 0u64) == 0; adler_byte_sum_u64(bytes, 1u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]); adler_byte_sum_u64(bytes, 2u64) == adler_byte_sum_u64(bytes, 1u64) + to_integer(bytes[1u64]); adler_byte_sum_u64(bytes, 3u64) == adler_byte_sum_u64(bytes, 2u64) + to_integer(bytes[2u64]); }; }
  have 1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { arithmetic() using {}; }
  unfold(adler_spec_a_u64(bytes, 3u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 3u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  rewrite(1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  simp();
 }
 ensures adler_spec_b_u64(bytes, 3u64, 1, 0) == truncating_remainder(3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 3));
  apply(adler_weighted_append_u64(bytes, 1u64, 3));
  apply(adler_weighted_append_u64(bytes, 2u64, 3));
  apply(adler_weighted_append_u64(bytes, 3u64, 3));
  have adler_weighted_sum_u64(bytes, 3u64, 3) == 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { arithmetic() using { adler_weighted_sum_u64(bytes, 0u64, 3) == 0; adler_weighted_sum_u64(bytes, 1u64, 3) == adler_weighted_sum_u64(bytes, 0u64, 3) + 3 * to_integer(bytes[0u64]); adler_weighted_sum_u64(bytes, 2u64, 3) == adler_weighted_sum_u64(bytes, 1u64, 3) + 2 * to_integer(bytes[1u64]); adler_weighted_sum_u64(bytes, 3u64, 3) == adler_weighted_sum_u64(bytes, 2u64, 3) + 1 * to_integer(bytes[2u64]); }; }
  have 3 + (3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { arithmetic() using {}; }
  unfold(adler_spec_b_u64(bytes, 3u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 3u64, 3) == 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  rewrite(3 + (3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  simp();
 }
}

// Extensionality uses only equality of the selected input bytes; it grants no memory authority.
theorem adler_sums_extensional_u64(left: uint8[], right: uint8[], bound: uint64, n: uint64, weight: Integer) {
 requires n <= bound;
 requires forall (k: uint64) { k < bound implies left[k] == right[k] };
 ensures adler_byte_sum_u64(left, n) == adler_byte_sum_u64(right, n) and adler_weighted_sum_u64(left, n, weight) == adler_weighted_sum_u64(right, n, weight) by {
  induct(n) as ih;
  if n <= 0u64 {
   apply(adler_sum_empty_u64(left, weight));
   apply(adler_sum_empty_u64(right, weight));
   have n == 0u64 by arithmetic() using { n <= 0u64; };
   rewrite(n == 0u64);
   rewrite(adler_byte_sum_u64(left, 0u64) == 0);
   rewrite(adler_byte_sum_u64(right, 0u64) == 0);
   rewrite(adler_weighted_sum_u64(left, 0u64, weight) == 0);
   rewrite(adler_weighted_sum_u64(right, 0u64, weight) == 0);
   both { normalize(); } and { normalize(); }
  } else {
   have 0u64 < n by simp();
   have n - 1u64 < n by arithmetic() using { 0u64 < n; };
   have n - 1u64 <= bound by arithmetic() using { n <= bound; 0u64 < n; };
   have n - 1u64 < bound by arithmetic() using { n <= bound; 0u64 < n; };
   apply(ih(n - 1u64)) using {
    n - 1u64 < n; n - 1u64 <= bound;
    forall (k: uint64) { k < bound implies left[k] == right[k] };
   };
   instantiate(forall (k: uint64) { k < bound implies left[k] == right[k] }, n - 1u64) using { n - 1u64 < bound; };
   apply(adler_sum_append_u64(left, n)) using { 0u64 < n; };
   apply(adler_sum_append_u64(right, n)) using { 0u64 < n; };
   apply(adler_weighted_append_u64(left, n, weight)) using { 0u64 < n; };
   apply(adler_weighted_append_u64(right, n, weight)) using { 0u64 < n; };
   both {
    rewrite(adler_byte_sum_u64(left, n) == adler_byte_sum_u64(left, n - 1u64) + to_integer(left[n - 1u64]));
    rewrite(adler_byte_sum_u64(right, n) == adler_byte_sum_u64(right, n - 1u64) + to_integer(right[n - 1u64]));
    rewrite(adler_byte_sum_u64(left, n - 1u64) == adler_byte_sum_u64(right, n - 1u64));
    rewrite(left[n - 1u64] == right[n - 1u64]);
    normalize();
   } and {
    rewrite(adler_weighted_sum_u64(left, n, weight) == adler_weighted_sum_u64(left, n - 1u64, weight) + (weight - to_integer(n - 1u64)) * to_integer(left[n - 1u64]));
    rewrite(adler_weighted_sum_u64(right, n, weight) == adler_weighted_sum_u64(right, n - 1u64, weight) + (weight - to_integer(n - 1u64)) * to_integer(right[n - 1u64]));
    rewrite(adler_weighted_sum_u64(left, n - 1u64, weight) == adler_weighted_sum_u64(right, n - 1u64, weight));
    rewrite(left[n - 1u64] == right[n - 1u64]);
    normalize();
   }
  }
 }
}

theorem adler_spec_extensional_u64(left: uint8[], right: uint8[], length: uint64, a0: Integer, b0: Integer) {
 requires forall (k: uint64) { k < length implies left[k] == right[k] };
 ensures adler_spec_a_u64(left, length, a0) == adler_spec_a_u64(right, length, a0) and adler_spec_b_u64(left, length, a0, b0) == adler_spec_b_u64(right, length, a0, b0) by {
  apply(adler_sums_extensional_u64(left, right, length, length, to_integer(length))) using {
   length <= length;
   forall (k: uint64) { k < length implies left[k] == right[k] };
  };
  both {
   unfold(adler_spec_a_u64(left, length, a0));
   unfold(adler_spec_a_u64(right, length, a0));
   rewrite(adler_byte_sum_u64(left, length) == adler_byte_sum_u64(right, length));
   normalize();
  } and {
   unfold(adler_spec_b_u64(left, length, a0, b0));
   unfold(adler_spec_b_u64(right, length, a0, b0));
   rewrite(adler_weighted_sum_u64(left, length, to_integer(length)) == adler_weighted_sum_u64(right, length, to_integer(length)));
   normalize();
  }
 }
}
