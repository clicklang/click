import click::integer;

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
 ensures adler_byte_sum_u64(bytes, 0u64) == 0 by { unfold(adler_byte_sum_u64(bytes, 0u64)); solve(); }
 ensures adler_weighted_sum_u64(bytes, 0u64, weight_end) == 0 by { unfold(adler_weighted_sum_u64(bytes, 0u64, weight_end)); solve(); }
}

theorem adler_sum_append_u64(bytes: uint8[], n: uint64) {
 requires 0u64 < n;
 ensures adler_byte_sum_u64(bytes, n) == adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]) by {
  have to_integer(0u64) <= to_integer(n - 1u64) by known();
  have to_integer(n - 1u64) < to_integer(18446744073709551615u64) by close() using { 0u64 < n; };
  unfold(adler_byte_sum_u64(bytes, n));
  known();
 }
}

theorem adler_weighted_append_u64(bytes: uint8[], n: uint64, weight_end: Integer) {
 requires 0u64 < n;
 ensures adler_weighted_sum_u64(bytes, n, weight_end) == adler_weighted_sum_u64(bytes, n - 1u64, weight_end) + (weight_end - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]) by {
  have to_integer(0u64) <= to_integer(n - 1u64) by known();
  have to_integer(n - 1u64) < to_integer(18446744073709551615u64) by close() using { 0u64 < n; };
  unfold(adler_weighted_sum_u64(bytes, n, weight_end));
  known();
 }
}

theorem adler_weight_shift_u64(bytes: uint8[], n: uint64, w0: Integer, w1: Integer) {
 ensures adler_weighted_sum_u64(bytes, n, w1) - adler_weighted_sum_u64(bytes, n, w0) == (w1 - w0) * adler_byte_sum_u64(bytes, n) by {
  let ih = induct(n);
  if n <= 0u64 {
   have n == 0u64 by close() using { n <= 0u64; };
   rewrite(n, 0u64);
   apply(adler_sum_empty_u64(bytes, w1));
   apply(adler_sum_empty_u64(bytes, w0));
   rewrite(adler_weighted_sum_u64(bytes, 0u64, w1), 0);
   rewrite(adler_weighted_sum_u64(bytes, 0u64, w0), 0);
   rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
   close() using { };
  } else {
   have 0u64 < n by solve();
   have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
   apply(ih(n - 1u64));
   apply(adler_weighted_append_u64(bytes, n, w1));
   apply(adler_weighted_append_u64(bytes, n, w0));
   apply(adler_sum_append_u64(bytes, n));
   rewrite(adler_weighted_sum_u64(bytes, n, w1), adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
   rewrite(adler_weighted_sum_u64(bytes, n, w0), adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
   rewrite(adler_byte_sum_u64(bytes, n), adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
   have (adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) - (adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) == (adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0)) + (w1 - w0) * to_integer(bytes[n - 1u64]) by {
    close() using {  };
   }
   rewrite((adler_weighted_sum_u64(bytes, n - 1u64, w1) + (w1 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])) - (adler_weighted_sum_u64(bytes, n - 1u64, w0) + (w0 - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64])), (adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0)) + (w1 - w0) * to_integer(bytes[n - 1u64]));
   rewrite(adler_weighted_sum_u64(bytes, n - 1u64, w1) - adler_weighted_sum_u64(bytes, n - 1u64, w0), (w1 - w0) * adler_byte_sum_u64(bytes, n - 1u64));
   close() using {  };
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
  have 1u64 <= n by close() using { 0u64 < n; };
  have to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
  have to_integer(n) - to_integer(n - 1u64) == 1 by { close() using { to_integer(n - 1u64) == to_integer(n) - to_integer(1u64); }; }
  apply(adler_weight_shift_u64(bytes, n - 1u64, to_integer(n - 1u64), to_integer(n)));
  have adler_byte_sum_u64(bytes, n - 1u64) == (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64) by {
   rewrite(to_integer(n) - to_integer(n - 1u64), 1);
   close() using { };
  }
  have adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) == adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n - 1u64) by {
   rewrite(adler_byte_sum_u64(bytes, n - 1u64), (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64));
   close() using { adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) - adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) == (to_integer(n) - to_integer(n - 1u64)) * adler_byte_sum_u64(bytes, n - 1u64); to_integer(n) - to_integer(n - 1u64) == 1; };
  }
  apply(adler_weighted_append_u64(bytes, n, to_integer(n)));
  apply(adler_sum_append_u64(bytes, n));
  rewrite(adler_weighted_sum_u64(bytes, n, to_integer(n)), adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)) + (to_integer(n) - to_integer(n - 1u64)) * to_integer(bytes[n - 1u64]));
  rewrite(adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n)), adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n - 1u64));
  rewrite(to_integer(n) - to_integer(n - 1u64), 1);
  rewrite(adler_byte_sum_u64(bytes, n), adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
  close() using { };
 }
}

theorem adler_byte_bounds_u64(value: uint8) {
 ensures 0 <= to_integer(value) by {
  close() using {  };
 }
 ensures to_integer(value) <= 255 by {
  close() using {  };
 }
}

theorem adler_sum_nonnegative_u64(bytes: uint8[], n: uint64) {
 ensures 0 <= adler_byte_sum_u64(bytes, n) by {
  let ih = induct(n);
  if n <= 0u64 {
   have n == 0u64 by close() using { n <= 0u64; };
   rewrite(n, 0u64);
   apply(adler_sum_empty_u64(bytes, 0));
   rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
   close() using { };
  } else {
   have 0u64 < n by solve();
   have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
   apply(ih(n - 1u64));
   apply(adler_byte_bounds_u64(bytes[n - 1u64]));
   apply(adler_sum_append_u64(bytes, n));
   rewrite(adler_byte_sum_u64(bytes, n), adler_byte_sum_u64(bytes, n - 1u64) + to_integer(bytes[n - 1u64]));
   close() using { 0 <= adler_byte_sum_u64(bytes, n - 1u64); 0 <= to_integer(bytes[n - 1u64]); };
  }
 }
}
theorem adler_weighted_nonnegative_u64(bytes: uint8[], n: uint64) {
 ensures 0 <= adler_weighted_sum_u64(bytes, n, to_integer(n)) by {
  let ih = induct(n);
  if n <= 0u64 {
   have n == 0u64 by close() using { n <= 0u64; };
   rewrite(n, 0u64);
   apply(adler_sum_empty_u64(bytes, to_integer(n)));
   rewrite(adler_weighted_sum_u64(bytes, 0u64, to_integer(n)), 0);
   close() using { };
  } else {
   have 0u64 < n by solve();
   have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
   apply(ih(n - 1u64));
   apply(adler_sum_nonnegative_u64(bytes, n));
   apply(adler_weighted_prefix_step_u64(bytes, n));
   rewrite(adler_weighted_sum_u64(bytes, n, to_integer(n)), adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)) + adler_byte_sum_u64(bytes, n));
   close() using { 0 <= adler_weighted_sum_u64(bytes, n - 1u64, to_integer(n - 1u64)); 0 <= adler_byte_sum_u64(bytes, n); };
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
   have q <= -1 by { close() using { q < 0; }; }
   have n <= -1 by { close() using { n == q * 65521 + r; q <= -1; r <= 65520; }; }
   have not (0 <= n) by { close() using { n <= -1; }; }
   contradiction(0 <= n);
  } else {
   have 0 <= q by { close() using { not (q < 0); }; }
   have q * 65521 <= n by { close() using { n == q * 65521 + r; 0 <= r; }; }
   have n < (q + 1) * 65521 by { close() using { n == q * 65521 + r; r <= 65520; }; }
   have 0 < q + 1 by { close() using { 0 <= q; }; }
   apply(integer::positive_divisor_quotient_lower(n, 65521, q));
   apply(integer::positive_divisor_quotient_strict_upper(n, 65521, q + 1));
   have truncating_quotient(n, 65521) == q by { close() using { q <= truncating_quotient(n, 65521); truncating_quotient(n, 65521) < q + 1; }; }
   apply(integer::truncation_identity(n, 65521));
   close() using { n == q * 65521 + r; n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); truncating_quotient(n, 65521) == q; };
  }
 }
}

theorem adler_residue_add_u64(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
  apply(integer::truncation_identity(n, 65521));
  apply(integer::truncation_identity(m, 65521));
  apply(integer::nonnegative_dividend_remainder(n, 65521));
  apply(integer::nonnegative_dividend_remainder(m, 65521));
  have 0 <= n + m by { close() using { 0 <= n; 0 <= m; }; }
  have 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521) by { close() using { 0 <= truncating_remainder(n, 65521); 0 <= truncating_remainder(m, 65521); }; }
  apply(integer::truncation_identity(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521));
  apply(integer::nonnegative_dividend_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521));
  apply(integer::positive_divisor_remainder_upper(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521));
  have truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) <= 65520 by { close() using { truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) <= 65521 - 1; }; }
  have n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
   close() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); truncating_remainder(n, 65521) + truncating_remainder(m, 65521) == truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521); };
  }
  apply(adler_residue_unique_u64(n + m, truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521), truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)));
  known();
 }
}

function adler_spec_checksum_u64(bytes: uint8[], length: uint64, a0: Integer, b0: Integer) -> Integer {
 65536 * adler_spec_b_u64(bytes, length, a0, b0) + adler_spec_a_u64(bytes, length, a0)
}

theorem adler_spec_a_canonical_u64(bytes: uint8[], n: uint64, a0: Integer) {
 requires 0 <= a0;
 ensures 0 <= adler_spec_a_u64(bytes, n, a0) and adler_spec_a_u64(bytes, n, a0) <= 65520 by {
  apply(adler_sum_nonnegative_u64(bytes, n));
  have 0 <= a0 + adler_byte_sum_u64(bytes, n) by { close() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, n); }; }
  apply(integer::nonnegative_dividend_remainder(a0 + adler_byte_sum_u64(bytes, n), 65521));
  apply(integer::positive_divisor_remainder_upper(a0 + adler_byte_sum_u64(bytes, n), 65521));
  have truncating_remainder(a0 + adler_byte_sum_u64(bytes, n), 65521) <= 65520 by { close() using { truncating_remainder(a0 + adler_byte_sum_u64(bytes, n), 65521) <= 65521 - 1; }; }
  unfold(adler_spec_a_u64(bytes, n, a0));
  all { 0 <= (truncating_remainder((to_integer(a0) + adler_byte_sum_u64(bytes, n)), 65521) : Integer) => { known(); } (truncating_remainder((to_integer(a0) + adler_byte_sum_u64(bytes, n)), 65521) : Integer) <= 65520 => { known(); } }
 }
}

theorem adler_spec_b_canonical_u64(bytes: uint8[], n: uint64, a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_b_u64(bytes, n, a0, b0) and adler_spec_b_u64(bytes, n, a0, b0) <= 65520 by {
  apply(adler_weighted_nonnegative_u64(bytes, n));
  have 0 <= to_integer(n); have to_integer(n) <= 18446744073709551615;
  have 0 <= to_integer(n) * a0 by {
   close() using { 0 <= to_integer(n); to_integer(n) <= 18446744073709551615; 0 <= a0; a0 <= 65520; };
  }
  have 0 <= b0 + to_integer(n) * a0 by { close() using { 0 <= b0; 0 <= to_integer(n) * a0; }; }
  have 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)) by { close() using { 0 <= b0 + to_integer(n) * a0; 0 <= adler_weighted_sum_u64(bytes, n, to_integer(n)); }; }
  apply(integer::nonnegative_dividend_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521));
  apply(integer::positive_divisor_remainder_upper(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521));
  have truncating_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521) <= 65520 by { close() using { truncating_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum_u64(bytes, n, to_integer(n)), 65521) <= 65521 - 1; }; }
  unfold(adler_spec_b_u64(bytes, n, a0, b0));
  all { 0 <= (truncating_remainder((to_integer(b0) + (to_integer(n) * to_integer(a0)) + adler_weighted_sum_u64(bytes, n, to_integer(n))), 65521) : Integer) => { known(); } (truncating_remainder((to_integer(b0) + (to_integer(n) * to_integer(a0)) + adler_weighted_sum_u64(bytes, n, to_integer(n))), 65521) : Integer) <= 65520 => { known(); } }
 }
}

theorem adler_spec_packing_bounds_u64(bytes: uint8[], n: uint64, a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_checksum_u64(bytes, n, a0, b0) and adler_spec_checksum_u64(bytes, n, a0, b0) <= 4293984240 by {
  apply(adler_spec_a_canonical_u64(bytes, n, a0));
  apply(adler_spec_b_canonical_u64(bytes, n, a0, b0));
  unfold(adler_spec_checksum_u64(bytes, n, a0, b0));
  all {
      0 <= (((65536 * adler_spec_b_u64(bytes, n, a0, b0)) + adler_spec_a_u64(bytes, n, a0)) : Integer) => {
          close() using { 0 <= adler_spec_b_u64(bytes, n, a0, b0); 0 <= adler_spec_a_u64(bytes, n, a0); };
      }
      (((65536 * adler_spec_b_u64(bytes, n, a0, b0)) + adler_spec_a_u64(bytes, n, a0)) : Integer) <= 4293984240 => {
          close() using { adler_spec_b_u64(bytes, n, a0, b0) <= 65520; adler_spec_a_u64(bytes, n, a0) <= 65520; };
      }
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
  have a0 == 0 * 65521 + a0 by { close() using {}; }
  apply(adler_residue_unique_u64(a0, 0, a0));
  unfold(adler_spec_a_u64(bytes, 0u64, a0));
  rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
  close() using { truncating_remainder(a0, 65521) == a0; };
 }
 ensures adler_spec_b_u64(bytes, 0u64, a0, b0) == b0 by {
  apply(adler_sum_empty_u64(bytes, to_integer(0u64)));
  have b0 == 0 * 65521 + b0 by { close() using {}; }
  apply(adler_residue_unique_u64(b0, 0, b0));
  unfold(adler_spec_b_u64(bytes, 0u64, a0, b0));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, to_integer(0u64)), 0);
  have b0 + 0 * a0 + 0 == b0 by { close() using {}; }
  rewrite(b0 + 0 * a0 + 0, b0);
  close() using { truncating_remainder(b0, 65521) == b0; };
 }
}

theorem adler_byte_observation_same_index_u64(bytes: uint8[], i: uint64, j: uint64) {
 requires i == j;
 ensures to_integer(bytes[i]) == to_integer(bytes[j]) by { rewrite(i, j); known(); }
}
theorem adler_sum_append_four_u64(bytes: uint8[], n: uint64) {
 requires n <= 18446744073709551611u64;
 ensures adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) + to_integer(bytes[n + 1u64]) + to_integer(bytes[n + 2u64]) + to_integer(bytes[n + 3u64]) by {
  have to_integer(0u64) < to_integer(n + 1u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 1u64) - 1u64) == to_integer(n) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 1u64));
  have adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) by { close() using { adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, (n + 1u64) - 1u64) + to_integer(bytes[(n + 1u64) - 1u64]); to_integer((n + 1u64) - 1u64) == to_integer(n); }; }
  have to_integer(0u64) < to_integer(n + 2u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 2u64) - 1u64) == to_integer(n + 1u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 2u64));
  have to_integer(n + 1u64) == to_integer((n + 2u64) - 1u64) by { close() using { to_integer((n + 2u64) - 1u64) == to_integer(n + 1u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 1u64, (n + 2u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]) by { rewrite(to_integer(n + 1u64), to_integer((n + 2u64) - 1u64)); known(); }
  have to_integer(0u64) < to_integer(n + 3u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 3u64) - 1u64) == to_integer(n + 2u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 3u64));
  have to_integer(n + 2u64) == to_integer((n + 3u64) - 1u64) by { close() using { to_integer((n + 3u64) - 1u64) == to_integer(n + 2u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 2u64, (n + 3u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]) by { rewrite(to_integer(n + 2u64), to_integer((n + 3u64) - 1u64)); known(); }
  have to_integer(0u64) < to_integer(n + 4u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 4u64) - 1u64) == to_integer(n + 3u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 4u64));
  have to_integer(n + 3u64) == to_integer((n + 4u64) - 1u64) by { close() using { to_integer((n + 4u64) - 1u64) == to_integer(n + 3u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 3u64, (n + 4u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]) by { rewrite(to_integer(n + 3u64), to_integer((n + 4u64) - 1u64)); known(); }
  rewrite(adler_byte_sum_u64(bytes, n + 4u64), adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 3u64), adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 2u64), adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 1u64), adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]));
  close() using {};
 }
}

theorem adler_weighted_append_four_u64(bytes: uint8[], n: uint64) {
 requires n <= 18446744073709551611u64;
 ensures adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)) == adler_weighted_sum_u64(bytes, n, to_integer(n)) + 4 * adler_byte_sum_u64(bytes, n) + 4 * to_integer(bytes[n]) + 3 * to_integer(bytes[n + 1u64]) + 2 * to_integer(bytes[n + 2u64]) + to_integer(bytes[n + 3u64]) by {
  have to_integer(0u64) < to_integer(n + 1u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 1u64) - 1u64) == to_integer(n) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 1u64));
  have adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]) by { close() using { adler_byte_sum_u64(bytes, n + 1u64) == adler_byte_sum_u64(bytes, (n + 1u64) - 1u64) + to_integer(bytes[(n + 1u64) - 1u64]); to_integer((n + 1u64) - 1u64) == to_integer(n); }; }
  have to_integer(0u64) < to_integer(n + 2u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 2u64) - 1u64) == to_integer(n + 1u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 2u64));
  have to_integer(n + 1u64) == to_integer((n + 2u64) - 1u64) by { close() using { to_integer((n + 2u64) - 1u64) == to_integer(n + 1u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 1u64, (n + 2u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 2u64) == adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]) by { rewrite(to_integer(n + 1u64), to_integer((n + 2u64) - 1u64)); known(); }
  have to_integer(0u64) < to_integer(n + 3u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 3u64) - 1u64) == to_integer(n + 2u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 3u64));
  have to_integer(n + 2u64) == to_integer((n + 3u64) - 1u64) by { close() using { to_integer((n + 3u64) - 1u64) == to_integer(n + 2u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 2u64, (n + 3u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 3u64) == adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]) by { rewrite(to_integer(n + 2u64), to_integer((n + 3u64) - 1u64)); known(); }
  have to_integer(0u64) < to_integer(n + 4u64) by { close() using { n <= 18446744073709551611u64; }; }
  have to_integer((n + 4u64) - 1u64) == to_integer(n + 3u64) by { close() using { n <= 18446744073709551611u64; }; }
  apply(adler_sum_append_u64(bytes, n + 4u64));
  have to_integer(n + 3u64) == to_integer((n + 4u64) - 1u64) by { close() using { to_integer((n + 4u64) - 1u64) == to_integer(n + 3u64); }; }
  apply(adler_byte_observation_same_index_u64(bytes, n + 3u64, (n + 4u64) - 1u64));
  have adler_byte_sum_u64(bytes, n + 4u64) == adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]) by { rewrite(to_integer(n + 3u64), to_integer((n + 4u64) - 1u64)); known(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 1u64));
  have adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) == adler_weighted_sum_u64(bytes, n, to_integer(n)) + adler_byte_sum_u64(bytes, n + 1u64) by { close() using { adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) == adler_weighted_sum_u64(bytes, (n + 1u64) - 1u64, to_integer((n + 1u64) - 1u64)) + adler_byte_sum_u64(bytes, n + 1u64); to_integer((n + 1u64) - 1u64) == to_integer(n); }; }
  apply(adler_weighted_prefix_step_u64(bytes, n + 2u64));
  have adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) == adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) + adler_byte_sum_u64(bytes, n + 2u64) by { rewrite(to_integer(n + 1u64), to_integer((n + 2u64) - 1u64)); known(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 3u64));
  have adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) == adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) + adler_byte_sum_u64(bytes, n + 3u64) by { rewrite(to_integer(n + 2u64), to_integer((n + 3u64) - 1u64)); known(); }
  apply(adler_weighted_prefix_step_u64(bytes, n + 4u64));
  have adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)) == adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) + adler_byte_sum_u64(bytes, n + 4u64) by { rewrite(to_integer(n + 3u64), to_integer((n + 4u64) - 1u64)); known(); }
  rewrite(adler_weighted_sum_u64(bytes, n + 4u64, to_integer(n + 4u64)), adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)) + adler_byte_sum_u64(bytes, n + 4u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 3u64, to_integer(n + 3u64)), adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)) + adler_byte_sum_u64(bytes, n + 3u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 2u64, to_integer(n + 2u64)), adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)) + adler_byte_sum_u64(bytes, n + 2u64));
  rewrite(adler_weighted_sum_u64(bytes, n + 1u64, to_integer(n + 1u64)), adler_weighted_sum_u64(bytes, n, to_integer(n)) + adler_byte_sum_u64(bytes, n + 1u64));
  rewrite(adler_byte_sum_u64(bytes, n + 4u64), adler_byte_sum_u64(bytes, n + 3u64) + to_integer(bytes[n + 3u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 3u64), adler_byte_sum_u64(bytes, n + 2u64) + to_integer(bytes[n + 2u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 2u64), adler_byte_sum_u64(bytes, n + 1u64) + to_integer(bytes[n + 1u64]));
  rewrite(adler_byte_sum_u64(bytes, n + 1u64), adler_byte_sum_u64(bytes, n) + to_integer(bytes[n]));
  close() using {};
 }
}// A signed quotient difference can witness congruence even when either
// representative is smaller. Both dividend interpretations remain nonnegative.
theorem adler_residue_congruent_u64(n: Integer, m: Integer, q: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 requires n == m + 65521 * q;
 ensures truncating_remainder(n, 65521) == truncating_remainder(m, 65521) by {
  apply(integer::truncation_identity(m, 65521));
  apply(integer::nonnegative_dividend_remainder(m, 65521));
  apply(integer::positive_divisor_remainder_upper(m, 65521));
  have truncating_remainder(m, 65521) <= 65520 by { close() using { truncating_remainder(m, 65521) <= 65521 - 1; }; }
  have n == (truncating_quotient(m, 65521) + q) * 65521 + truncating_remainder(m, 65521) by {
   close() using { n == m + 65521 * q; m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); };
  }
  apply(adler_residue_unique_u64(n, truncating_quotient(m, 65521) + q, truncating_remainder(m, 65521)));
  known();
 }
}

theorem adler_spec_one_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 1u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 1));
  apply(adler_sum_append_u64(bytes, 1u64));
  unfold(adler_spec_a_u64(bytes, 1u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 1u64), adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]));
  rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
  solve();
 }
 ensures adler_spec_b_u64(bytes, 1u64, 1, 0) == truncating_remainder(1 + to_integer(bytes[0u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 1));
  apply(adler_weighted_append_u64(bytes, 1u64, 1));
  unfold(adler_spec_b_u64(bytes, 1u64, 1, 0));
  have adler_weighted_sum_u64(bytes, 1u64, 1) == adler_weighted_sum_u64(bytes, 0u64, 1) + to_integer(bytes[0u64]) by { close() using { adler_weighted_sum_u64(bytes, 1u64, 1) == adler_weighted_sum_u64(bytes, 0u64, 1) + (1 - 0) * to_integer(bytes[0u64]); }; }
  rewrite(adler_weighted_sum_u64(bytes, 1u64, 1), adler_weighted_sum_u64(bytes, 0u64, 1) + to_integer(bytes[0u64]));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, 1), 0);
  solve();
 }
}

theorem adler_byte_offset_association_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures to_integer((bytes + prefix)[suffix]) == to_integer(bytes[prefix + suffix]) by {
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have (bytes + prefix) + suffix == bytes + (prefix + suffix) by { close() using { to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix); }; }
  rewrite((bytes + prefix) + suffix, bytes + (prefix + suffix));
  solve();
 }
}

theorem adler_sum_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures adler_byte_sum_u64(bytes, prefix + suffix) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix) by {
  let ih = induct(suffix);
  if suffix <= 0u64 {
   have suffix == 0u64 by close() using { suffix <= 0u64; };
   have to_integer(prefix + suffix) == to_integer(prefix) by { rewrite(suffix, 0u64); known(); }
   apply(adler_sum_empty_u64(bytes + prefix, 0));
   have adler_byte_sum_u64(bytes + prefix, suffix) == 0 by { rewrite(suffix, 0u64); known(); }
   rewrite(to_integer(prefix + suffix), to_integer(prefix));
   rewrite(adler_byte_sum_u64(bytes + prefix, suffix), 0); solve();
  } else {
   have 0u64 < suffix by solve();
   have to_integer(suffix - 1u64) < to_integer(suffix) by close() using { 0u64 < suffix; };
   have 1u64 <= suffix by close() using { 0u64 < suffix; };
   have to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   have to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615 by close() using {
    to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(ih(suffix - 1u64));
   have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   have to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
   have to_integer(0u64) < to_integer(prefix + suffix) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   have to_integer(0u64) < to_integer(prefix + suffix) by known();
   have to_integer(1u64) <= to_integer(prefix + suffix) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by known();
   apply(adler_sum_append_u64(bytes, prefix + suffix));
   apply(adler_sum_append_u64(bytes + prefix, suffix));
   apply(adler_byte_offset_association_u64(bytes, prefix, suffix - 1u64));
   have adler_byte_sum_u64(bytes, (prefix + suffix) - 1u64) == adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix - 1u64) by {
    rewrite(to_integer((prefix + suffix) - 1u64), to_integer(prefix + (suffix - 1u64))); known();
   }
   have to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite(to_integer((prefix + suffix) - 1u64), to_integer(prefix + (suffix - 1u64))); rewrite(to_integer((bytes + prefix)[suffix - 1u64]), to_integer(bytes[prefix + (suffix - 1u64)])); solve();
   }
   close() using {
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
  let ih = induct(suffix);
  if suffix <= 0u64 {
   have suffix == 0u64 by close() using { suffix <= 0u64; };
   have to_integer(prefix + suffix) == to_integer(prefix) by { rewrite(suffix, 0u64); known(); }
   apply(adler_sum_empty_u64(bytes + prefix, weight_end - to_integer(prefix)));
   have adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)) == 0 by { rewrite(suffix, 0u64); known(); }
   rewrite(to_integer(prefix + suffix), to_integer(prefix));
   rewrite(adler_weighted_sum_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)), 0); solve();
  } else {
   have 0u64 < suffix by solve();
   have to_integer(suffix - 1u64) < to_integer(suffix) by close() using { 0u64 < suffix; };
   have 1u64 <= suffix by close() using { 0u64 < suffix; };
   have to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   have to_integer(prefix) + to_integer(suffix - 1u64) <= 18446744073709551615 by close() using {
    to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   apply(ih(suffix - 1u64));
   have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   have to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
   have to_integer(0u64) < to_integer(prefix + suffix) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   have to_integer(0u64) < to_integer(prefix + suffix) by known();
   have to_integer(1u64) <= to_integer(prefix + suffix) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    0 <= to_integer(prefix);
    to_integer(1u64) <= to_integer(suffix);
   };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1u64)) == to_integer(prefix) + to_integer(suffix - 1u64);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   have to_integer((prefix + suffix) - 1u64) == to_integer(prefix + (suffix - 1u64)) by known();
   apply(adler_weighted_append_u64(bytes, prefix + suffix, weight_end));
   apply(adler_weighted_append_u64(bytes + prefix, suffix, weight_end - to_integer(prefix)));
   apply(adler_byte_offset_association_u64(bytes, prefix, suffix - 1u64));
   have adler_weighted_sum_u64(bytes, (prefix + suffix) - 1u64, weight_end) == adler_weighted_sum_u64(bytes, prefix, weight_end) + adler_weighted_sum_u64(bytes + prefix, suffix - 1u64, weight_end - to_integer(prefix)) by {
    rewrite(to_integer((prefix + suffix) - 1u64), to_integer(prefix + (suffix - 1u64))); known();
   }
   have to_integer(bytes[(prefix + suffix) - 1u64]) == to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite(to_integer((prefix + suffix) - 1u64), to_integer(prefix + (suffix - 1u64))); rewrite(to_integer((bytes + prefix)[suffix - 1u64]), to_integer(bytes[prefix + (suffix - 1u64)])); solve();
   }
   have weight_end - to_integer((prefix + suffix) - 1u64) == (weight_end - to_integer(prefix)) - to_integer(suffix - 1u64) by close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer((prefix + suffix) - 1u64) == to_integer(prefix + suffix) - to_integer(1u64);
    to_integer(suffix - 1u64) == to_integer(suffix) - to_integer(1u64);
   };
   have (weight_end - to_integer((prefix + suffix) - 1u64)) * to_integer(bytes[(prefix + suffix) - 1u64]) == ((weight_end - to_integer(prefix)) - to_integer(suffix - 1u64)) * to_integer((bytes + prefix)[suffix - 1u64]) by {
    rewrite(weight_end - to_integer((prefix + suffix) - 1u64), (weight_end - to_integer(prefix)) - to_integer(suffix - 1u64));
    rewrite(to_integer(bytes[(prefix + suffix) - 1u64]), to_integer((bytes + prefix)[suffix - 1u64]));
    solve();
   }
   close() using {
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
  apply(integer::truncation_identity(n, 65521));
  apply(integer::nonnegative_dividend_remainder(n, 65521));
  have 0 <= n + m by { close() using { 0 <= n; 0 <= m; }; }
  have 0 <= truncating_remainder(n, 65521) + m by { close() using { 0 <= truncating_remainder(n, 65521); 0 <= m; }; }
  have n + m == (truncating_remainder(n, 65521) + m) + 65521 * truncating_quotient(n, 65521) by { close() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); }; }
  apply(adler_residue_congruent_u64(n + m, truncating_remainder(n, 65521) + m, truncating_quotient(n, 65521)));
  known();
 }
}

theorem adler_spec_a_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64, a0: Integer) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 requires 0 <= a0;
 ensures adler_spec_a_u64(bytes, prefix + suffix, a0) == adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)) by {
  apply(adler_sum_concat_u64(bytes, prefix, suffix));
  apply(adler_sum_nonnegative_u64(bytes, prefix));
  apply(adler_sum_nonnegative_u64(bytes + prefix, suffix));
  have 0 <= a0 + adler_byte_sum_u64(bytes, prefix) by { close() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, prefix); }; }
  apply(adler_residue_add_left_u64(a0 + adler_byte_sum_u64(bytes, prefix), adler_byte_sum_u64(bytes + prefix, suffix)));
  unfold(adler_spec_a_u64(bytes, prefix + suffix, a0));
  unfold(adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)));
  unfold(adler_spec_a_u64(bytes, prefix, a0));
  rewrite(adler_byte_sum_u64(bytes, prefix + suffix), adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix));
  have a0 + (adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix)) == (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_byte_sum_u64(bytes + prefix, suffix) by { close() using {}; }
  rewrite(a0 + (adler_byte_sum_u64(bytes, prefix) + adler_byte_sum_u64(bytes + prefix, suffix)), (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_byte_sum_u64(bytes + prefix, suffix));
  known();
 }
}

theorem adler_sum_upper_u64(bytes: uint8[], n: uint64) {
 ensures adler_byte_sum_u64(bytes, n) <= 255 * to_integer(n) by {
  let ih = induct(n);
  if n <= 0u64 {
   have n == 0u64 by close() using { n <= 0u64; };
   apply(adler_sum_empty_u64(bytes, 0));
   rewrite(n, 0u64);
   close() using { adler_byte_sum_u64(bytes, 0u64) == 0; };
  } else {
   have 0u64 < n by solve();
   have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
   apply(ih(n - 1u64));
   apply(adler_sum_append_u64(bytes, n));
   apply(adler_byte_bounds_u64(bytes[n - 1u64]));
   have 1u64 <= n by close() using { 0u64 < n; };
   have to_integer(n - 1u64) == to_integer(n) - to_integer(1u64);
   close() using {
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
  rewrite(y, qb * 65521 + rb);
  rewrite(x, qa * 65521 + ra);
  close() using {  };
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
  apply(integer::truncation_identity(x, 65521));
  apply(integer::truncation_identity(y, 65521));
  apply(integer::nonnegative_dividend_remainder(x, 65521));
  apply(integer::nonnegative_dividend_remainder(y, 65521));
  apply(integer::positive_divisor_remainder_upper(x, 65521));
  have truncating_remainder(x, 65521) <= 65520 by { close() using { truncating_remainder(x, 65521) <= 65521 - 1; }; }
  have 0 <= k * x by { close() using { 0 <= k; k <= 18446744073709551615; 0 <= x; x <= 4703919738795935727345; }; }
  have 0 <= k * truncating_remainder(x, 65521) by { close() using { 0 <= k; k <= 18446744073709551615; 0 <= truncating_remainder(x, 65521); truncating_remainder(x, 65521) <= 65520; }; }
  have 0 <= y + k * x + z by { close() using { 0 <= y; 0 <= k * x; 0 <= z; }; }
  have 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z by { close() using { 0 <= truncating_remainder(y, 65521); 0 <= k * truncating_remainder(x, 65521); 0 <= z; }; }
  apply(adler_seed_polynomial_u64(x, y, k, z, truncating_quotient(x, 65521), truncating_remainder(x, 65521), truncating_quotient(y, 65521), truncating_remainder(y, 65521)));
  apply(adler_residue_congruent_u64(y + k * x + z, truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, truncating_quotient(y, 65521) + k * truncating_quotient(x, 65521)));
  known();
 }
}

theorem adler_concat_index_partition_u64(prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures defined((prefix + suffix) - prefix) and to_integer((prefix + suffix) - prefix) == to_integer(suffix) by {
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have to_integer(prefix) <= to_integer(prefix + suffix) by close() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   0 <= to_integer(suffix);
  };
  have to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
  have to_integer((prefix + suffix) - prefix) == to_integer(suffix) by close() using {
   to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  };
  all { defined(((prefix + suffix) - prefix)) => { known(); } to_integer(((prefix + suffix) - prefix)) == to_integer(suffix) => { known(); } }
 }
}

theorem adler_weighted_prefix_concat_u64(bytes: uint8[], prefix: uint64, suffix: uint64) {
 requires to_integer(prefix) + to_integer(suffix) <= 18446744073709551615;
 ensures adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)) by {
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have to_integer(prefix + suffix) - to_integer(prefix) == to_integer(suffix) by close() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  };
  apply(adler_weighted_concat_u64(bytes, prefix, suffix, to_integer(prefix + suffix)));
  have adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)) by {
   rewrite(to_integer(suffix), to_integer(prefix + suffix) - to_integer(prefix));
   known();
  }
  apply(adler_weight_shift_u64(bytes, prefix, to_integer(prefix), to_integer(prefix + suffix)));
  have adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) - adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) == to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) by {
   rewrite(to_integer(suffix), to_integer(prefix + suffix) - to_integer(prefix));
   known();
  }
  close() using {
   adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)) == adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix));
   adler_weighted_sum_u64(bytes, prefix, to_integer(prefix + suffix)) - adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) == to_integer(suffix) * adler_byte_sum_u64(bytes, prefix);
  };
 }
}
theorem adler_join_seed_polynomial_u64(a0: Integer, b0: Integer, p: Integer, s: Integer, sp: Integer, wp: Integer, wt: Integer) {
 ensures b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt by {
  close() using {  };
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
  have 0 <= to_integer(suffix); have to_integer(suffix) <= 18446744073709551615;
  have 0 <= to_integer(prefix) * a0 by { close() using { 0 <= to_integer(prefix); to_integer(prefix) <= 18446744073709551615; 0 <= a0; a0 <= 65520; }; }
  have 0 <= a0 + adler_byte_sum_u64(bytes, prefix) by { close() using { 0 <= a0; 0 <= adler_byte_sum_u64(bytes, prefix); }; }
  have 255 * to_integer(prefix) <= 4703919738795935661825 by { close() using { to_integer(prefix) <= 18446744073709551615; }; }
  have adler_byte_sum_u64(bytes, prefix) <= 4703919738795935661825 by { close() using {
   adler_byte_sum_u64(bytes, prefix) <= 255 * to_integer(prefix);
   255 * to_integer(prefix) <= 4703919738795935661825;
  }; }
  have a0 + adler_byte_sum_u64(bytes, prefix) <= 4703919738795935727345 by { close() using {
   a0 <= 65520; adler_byte_sum_u64(bytes, prefix) <= 4703919738795935661825;
  }; }
  have 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) by { close() using { 0 <= b0; 0 <= to_integer(prefix) * a0; 0 <= adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)); }; }
  apply(adler_residue_seed_update_u64(a0 + adler_byte_sum_u64(bytes, prefix), b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)), to_integer(suffix), adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))));
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  apply(adler_join_seed_polynomial_u64(a0, b0, to_integer(prefix), to_integer(suffix), adler_byte_sum_u64(bytes, prefix), adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)), adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))));
  unfold(adler_spec_b_u64(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_b_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)));
  unfold(adler_spec_a_u64(bytes, prefix, a0));
  unfold(adler_spec_b_u64(bytes, prefix, a0, b0));
  rewrite(adler_weighted_sum_u64(bytes, prefix + suffix, to_integer(prefix + suffix)), adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)));
  rewrite(to_integer(prefix + suffix), to_integer(prefix) + to_integer(suffix));
  rewrite(b0 + (to_integer(prefix) + to_integer(suffix)) * a0 + (adler_weighted_sum_u64(bytes, prefix, to_integer(prefix)) + to_integer(suffix) * adler_byte_sum_u64(bytes, prefix) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix))), (b0 + to_integer(prefix) * a0 + adler_weighted_sum_u64(bytes, prefix, to_integer(prefix))) + to_integer(suffix) * (a0 + adler_byte_sum_u64(bytes, prefix)) + adler_weighted_sum_u64(bytes + prefix, suffix, to_integer(suffix)));
  known();
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
  rewrite(adler_spec_a_u64(bytes, prefix + suffix, a0), adler_spec_a_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0)));
  rewrite(adler_spec_b_u64(bytes, prefix + suffix, a0, b0), adler_spec_b_u64(bytes + prefix, suffix, adler_spec_a_u64(bytes, prefix, a0), adler_spec_b_u64(bytes, prefix, a0, b0)));
  solve();
 }
}

theorem adler_spec_four_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 4u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 0));
  apply(adler_sum_append_four_u64(bytes, 0u64));
  have 1 + (0 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]) by { close() using {}; }
  unfold(adler_spec_a_u64(bytes, 4u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 4u64), adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64]));
  rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
  rewrite(1 + (0 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])), 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) + to_integer(bytes[3u64])); solve();
 }
 ensures adler_spec_b_u64(bytes, 4u64, 1, 0) == truncating_remainder(4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 0));
  apply(adler_weighted_append_four_u64(bytes, 0u64));
  have 0 + 4 * 1 + (0 + 4 * 0 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])) == 4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]) by { close() using {}; }
  unfold(adler_spec_b_u64(bytes, 4u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 4u64, 4), adler_weighted_sum_u64(bytes, 0u64, 0) + 4 * adler_byte_sum_u64(bytes, 0u64) + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64]));
  rewrite(adler_weighted_sum_u64(bytes, 0u64, 0), 0);
  rewrite(adler_byte_sum_u64(bytes, 0u64), 0);
  rewrite(0 + 4 * 1 + (0 + 4 * 0 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])), 4 + 4 * to_integer(bytes[0u64]) + 3 * to_integer(bytes[1u64]) + 2 * to_integer(bytes[2u64]) + to_integer(bytes[3u64])); solve();
 }
}

theorem adler_spec_two_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 2u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 2));
  apply(adler_sum_append_u64(bytes, 1u64));
  apply(adler_sum_append_u64(bytes, 2u64));
  have adler_byte_sum_u64(bytes, 2u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { close() using { adler_byte_sum_u64(bytes, 0u64) == 0; adler_byte_sum_u64(bytes, 1u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]); adler_byte_sum_u64(bytes, 2u64) == adler_byte_sum_u64(bytes, 1u64) + to_integer(bytes[1u64]); }; }
  have 1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { close() using {}; }
  unfold(adler_spec_a_u64(bytes, 2u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 2u64), to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  rewrite(1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64])), 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  solve();
 }
 ensures adler_spec_b_u64(bytes, 2u64, 1, 0) == truncating_remainder(2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 2));
  apply(adler_weighted_append_u64(bytes, 1u64, 2));
  apply(adler_weighted_append_u64(bytes, 2u64, 2));
  have adler_weighted_sum_u64(bytes, 2u64, 2) == 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { close() using { adler_weighted_sum_u64(bytes, 0u64, 2) == 0; adler_weighted_sum_u64(bytes, 1u64, 2) == adler_weighted_sum_u64(bytes, 0u64, 2) + (2 - 0) * to_integer(bytes[0u64]); adler_weighted_sum_u64(bytes, 2u64, 2) == adler_weighted_sum_u64(bytes, 1u64, 2) + (2 - 1) * to_integer(bytes[1u64]); }; }
  have 0 + 2 * 1 + (2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64])) == 2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]) by { close() using {}; }
  unfold(adler_spec_b_u64(bytes, 2u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 2u64, 2), 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  rewrite(0 + 2 * 1 + (2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64])), 2 + 2 * to_integer(bytes[0u64]) + to_integer(bytes[1u64]));
  solve();
 }
}

theorem adler_spec_three_u64(bytes: uint8[]) {
 ensures adler_spec_a_u64(bytes, 3u64, 1) == truncating_remainder(1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 3));
  apply(adler_sum_append_u64(bytes, 1u64));
  apply(adler_sum_append_u64(bytes, 2u64));
  apply(adler_sum_append_u64(bytes, 3u64));
  have adler_byte_sum_u64(bytes, 3u64) == to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { close() using { adler_byte_sum_u64(bytes, 0u64) == 0; adler_byte_sum_u64(bytes, 1u64) == adler_byte_sum_u64(bytes, 0u64) + to_integer(bytes[0u64]); adler_byte_sum_u64(bytes, 2u64) == adler_byte_sum_u64(bytes, 1u64) + to_integer(bytes[1u64]); adler_byte_sum_u64(bytes, 3u64) == adler_byte_sum_u64(bytes, 2u64) + to_integer(bytes[2u64]); }; }
  have 1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { close() using {}; }
  unfold(adler_spec_a_u64(bytes, 3u64, 1));
  rewrite(adler_byte_sum_u64(bytes, 3u64), to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  rewrite(1 + (to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64])), 1 + to_integer(bytes[0u64]) + to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  solve();
 }
 ensures adler_spec_b_u64(bytes, 3u64, 1, 0) == truncating_remainder(3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]), 65521) by {
  apply(adler_sum_empty_u64(bytes, 3));
  apply(adler_weighted_append_u64(bytes, 1u64, 3));
  apply(adler_weighted_append_u64(bytes, 2u64, 3));
  apply(adler_weighted_append_u64(bytes, 3u64, 3));
  have adler_weighted_sum_u64(bytes, 3u64, 3) == 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { close() using { adler_weighted_sum_u64(bytes, 0u64, 3) == 0; adler_weighted_sum_u64(bytes, 1u64, 3) == adler_weighted_sum_u64(bytes, 0u64, 3) + (3 - 0) * to_integer(bytes[0u64]); adler_weighted_sum_u64(bytes, 2u64, 3) == adler_weighted_sum_u64(bytes, 1u64, 3) + (3 - 1) * to_integer(bytes[1u64]); adler_weighted_sum_u64(bytes, 3u64, 3) == adler_weighted_sum_u64(bytes, 2u64, 3) + (3 - 2) * to_integer(bytes[2u64]); }; }
  have 0 + 3 * 1 + (3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64])) == 3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]) by { close() using {}; }
  unfold(adler_spec_b_u64(bytes, 3u64, 1, 0));
  rewrite(adler_weighted_sum_u64(bytes, 3u64, 3), 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  rewrite(0 + 3 * 1 + (3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64])), 3 + 3 * to_integer(bytes[0u64]) + 2 * to_integer(bytes[1u64]) + to_integer(bytes[2u64]));
  solve();
 }
}

// Extensionality uses only equality of the selected input bytes; it grants no memory authority.
theorem adler_sums_extensional_u64(left: uint8[], right: uint8[], bound: uint64, n: uint64, weight: Integer) {
 requires n <= bound;
 requires forall (k: uint64) { k < bound implies left[k] == right[k] };
 ensures adler_byte_sum_u64(left, n) == adler_byte_sum_u64(right, n) and adler_weighted_sum_u64(left, n, weight) == adler_weighted_sum_u64(right, n, weight) by {
  let ih = induct(n);
  if n <= 0u64 {
   apply(adler_sum_empty_u64(left, weight));
   apply(adler_sum_empty_u64(right, weight));
   have n == 0u64 by close() using { n <= 0u64; };
   rewrite(n, 0u64);
   rewrite(adler_byte_sum_u64(left, 0u64), 0);
   rewrite(adler_byte_sum_u64(right, 0u64), 0);
   rewrite(adler_weighted_sum_u64(left, 0u64, weight), 0);
   rewrite(adler_weighted_sum_u64(right, 0u64, weight), 0);
   all { (0 : Integer) == 0 => { known(); } (0 : Integer) == 0 => { known(); } }
  } else {
   have 0u64 < n by solve();
   have to_integer(n - 1u64) < to_integer(n) by close() using { 0u64 < n; };
   have to_integer(n - 1u64) <= to_integer(bound) by close() using { n <= bound; 0u64 < n; };
   have to_integer(n - 1u64) < to_integer(bound) by close() using { n <= bound; 0u64 < n; };
   apply(ih(n - 1u64));
   have (n - 1u64) < bound;
   instantiate(forall (k: uint64) { k < bound implies left[k] == right[k] }, n - 1u64);
   apply(adler_sum_append_u64(left, n));
   apply(adler_sum_append_u64(right, n));
   apply(adler_weighted_append_u64(left, n, weight));
   apply(adler_weighted_append_u64(right, n, weight));
   all {
       adler_byte_sum_u64(left, n) == adler_byte_sum_u64(right, n) => {
           rewrite(adler_byte_sum_u64(left, n), adler_byte_sum_u64(left, n - 1u64) + to_integer(left[n - 1u64]));
           rewrite(adler_byte_sum_u64(right, n), adler_byte_sum_u64(right, n - 1u64) + to_integer(right[n - 1u64]));
           rewrite(adler_byte_sum_u64(left, n - 1u64), adler_byte_sum_u64(right, n - 1u64));
           rewrite(left[n - 1u64], right[n - 1u64]);
           known();
       }
       adler_weighted_sum_u64(left, n, weight) == adler_weighted_sum_u64(right, n, weight) => {
           rewrite(adler_weighted_sum_u64(left, n, weight), adler_weighted_sum_u64(left, n - 1u64, weight) + (weight - to_integer(n - 1u64)) * to_integer(left[n - 1u64]));
           rewrite(adler_weighted_sum_u64(right, n, weight), adler_weighted_sum_u64(right, n - 1u64, weight) + (weight - to_integer(n - 1u64)) * to_integer(right[n - 1u64]));
           rewrite(adler_weighted_sum_u64(left, n - 1u64, weight), adler_weighted_sum_u64(right, n - 1u64, weight));
           rewrite(left[n - 1u64], right[n - 1u64]);
           known();
       }
   }
  }
 }
}

theorem adler_spec_extensional_u64(left: uint8[], right: uint8[], length: uint64, a0: Integer, b0: Integer) {
 requires forall (k: uint64) { k < length implies left[k] == right[k] };
 ensures adler_spec_a_u64(left, length, a0) == adler_spec_a_u64(right, length, a0) and adler_spec_b_u64(left, length, a0, b0) == adler_spec_b_u64(right, length, a0, b0) by {
  apply(adler_sums_extensional_u64(left, right, length, length, to_integer(length)));
  all {
      adler_spec_a_u64(left, length, a0) == adler_spec_a_u64(right, length, a0) => {
          unfold(adler_spec_a_u64(left, length, a0));
          unfold(adler_spec_a_u64(right, length, a0));
          rewrite(adler_byte_sum_u64(left, length), adler_byte_sum_u64(right, length));
          known();
      }
      adler_spec_b_u64(left, length, a0, b0) == adler_spec_b_u64(right, length, a0, b0) => {
          unfold(adler_spec_b_u64(left, length, a0, b0));
          unfold(adler_spec_b_u64(right, length, a0, b0));
          rewrite(adler_weighted_sum_u64(left, length, to_integer(length)), adler_weighted_sum_u64(right, length, to_integer(length)));
          known();
      }
  }
 }
}
