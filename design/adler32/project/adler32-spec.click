import click::integer;

// Shared Adler-32 specification over a logical byte retained_state.
// The caller supplies a nonnegative signed-range length and canonical seeds.
// These are mathematical lemmas; neither implementation's result is assumed.

function adler_byte_sum(bytes: uint8[], end: int32) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer(bytes[k] as int32) })
}
function adler_weighted_sum(bytes: uint8[], end: int32, weight_end: int32) -> Integer {
 (0..end).fold(0, |acc, k| {
  acc + (to_integer(weight_end) - to_integer(k)) * to_integer(bytes[k] as int32)
 })
}
function adler_spec_a(bytes: uint8[], length: int32, a0: Integer) -> Integer {
 truncating_remainder(a0 + adler_byte_sum(bytes, length), 65521)
}
function adler_spec_b(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 truncating_remainder(b0 + to_integer(length) * a0 + adler_weighted_sum(bytes, length, length), 65521)
}
theorem adler_sum_empty(bytes: uint8[], weight_end: int32) {
 ensures adler_byte_sum(bytes, 0) == 0 by { unfold(adler_byte_sum(bytes, 0)); close(); }
 ensures adler_weighted_sum(bytes, 0, weight_end) == 0 by { unfold(adler_weighted_sum(bytes, 0, weight_end)); close(); }
}

theorem adler_sum_append(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer(bytes[n - 1] as int32) by {
  have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
  have to_integer(n - 1) < 2147483647 by { close() using { 0 < n; }; }
  unfold(adler_byte_sum(bytes, n));
  close();
 }
}
theorem adler_weighted_append(bytes: uint8[], n: int32, weight_end: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, weight_end) == adler_weighted_sum(bytes, n - 1, weight_end) + (to_integer(weight_end) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32) by {
  have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
  have to_integer(n - 1) < 2147483647 by { close() using { 0 < n; }; }
  unfold(adler_weighted_sum(bytes, n, weight_end));
  close();
 }
}

theorem adler_weight_shift(bytes: uint8[], n: int32, w0: int32, w1: int32) {
 requires 0 <= n;
 ensures adler_weighted_sum(bytes, n, w1) - adler_weighted_sum(bytes, n, w0) == (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n) by {
  let ih = induct(n);
  if n <= 0 {
   unfold(adler_weighted_sum(bytes, n, w1));
   unfold(adler_weighted_sum(bytes, n, w0));
   unfold(adler_byte_sum(bytes, n));
   have adler_weighted_sum(bytes, n, w1) == 0 by { close(); }
   have adler_weighted_sum(bytes, n, w0) == 0 by { close(); }
   have adler_byte_sum(bytes, n) == 0 by { close(); }
   close() using { adler_weighted_sum(bytes, n, w1) == 0; adler_weighted_sum(bytes, n, w0) == 0; adler_byte_sum(bytes, n) == 0; };
  } else {
   have 0 < n by { close(); }
   have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
   have to_integer(n - 1) < to_integer(n) by { close() using { 0 < n; }; }
   have to_integer(n - 1) < 2147483647 by { close() using { 0 < n; }; }
   have defined(n - 1) by { close() using { 0 < n; }; }
   apply(ih(n - 1));
   unfold(adler_weighted_sum(bytes, n, w1));
   unfold(adler_weighted_sum(bytes, n, w0));
   unfold(adler_byte_sum(bytes, n));
   have (adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32)) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32)) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer(bytes[n - 1] as int32) by {
    close() using {  };
   }
   rewrite((adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32)) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32)), (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer(bytes[n - 1] as int32));
   rewrite(adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0), (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n - 1));
   close() using {  };
  }
 }
}

theorem adler_weighted_prefix_step(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n) by {
  have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
  have defined(n - 1) by { close() using { 0 < n; }; }
  have to_integer(n - 1) == to_integer(n) - to_integer(1);
  have to_integer(n) - to_integer(n - 1) == 1 by { close() using { to_integer(n - 1) == to_integer(n) - to_integer(1); }; }
  apply(adler_weight_shift(bytes, n - 1, n - 1, n));
  have adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1) by {
   rewrite(to_integer(n) - to_integer(n - 1), 1);
   close() using { };
  }
  have adler_weighted_sum(bytes, n - 1, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1) by {
   rewrite(adler_byte_sum(bytes, n - 1), (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1));
   close() using { adler_weighted_sum(bytes, n - 1, n) - adler_weighted_sum(bytes, n - 1, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1); to_integer(n) - to_integer(n - 1) == 1; };
  }
  apply(adler_weighted_append(bytes, n, n));
  apply(adler_sum_append(bytes, n));
  rewrite(adler_weighted_sum(bytes, n, n), adler_weighted_sum(bytes, n - 1, n) + (to_integer(n) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32));
  rewrite(adler_weighted_sum(bytes, n - 1, n), adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1));
  rewrite(to_integer(n) - to_integer(n - 1), 1);
  rewrite(adler_byte_sum(bytes, n), adler_byte_sum(bytes, n - 1) + to_integer(bytes[n - 1] as int32));
  close() using { };
 }
}

theorem adler_byte_bounds(value: uint8) {
 ensures 0 <= to_integer(value as int32) by {
  have 0 <= value as int32 by { close(); }
  close();
 }
 ensures to_integer(value as int32) <= 255 by {
  have value as int32 <= 255 by { close(); }
  close();
 }
}


theorem adler_sum_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_byte_sum(bytes, n) by {
  let ih = induct(n);
  if n <= 0 {
   unfold(adler_byte_sum(bytes, n));
   close() using { adler_byte_sum(bytes, n) == 0; };
  } else {
   have 0 < n by { close(); }
   have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
   have to_integer(n - 1) < to_integer(n) by { close() using { 0 < n; }; }
   have defined(n - 1) by { close() using { 0 < n; }; }
   apply(ih(n - 1));
   apply(adler_byte_bounds(bytes[n - 1]));
   apply(adler_sum_append(bytes, n));
   rewrite(adler_byte_sum(bytes, n), adler_byte_sum(bytes, n - 1) + to_integer(bytes[n - 1] as int32));
   close() using { 0 <= adler_byte_sum(bytes, n - 1); 0 <= to_integer(bytes[n - 1] as int32); };
  }
 }
}
theorem adler_weighted_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_weighted_sum(bytes, n, n) by {
  let ih = induct(n);
  if n <= 0 {
   unfold(adler_weighted_sum(bytes, n, n));
   close() using { adler_weighted_sum(bytes, n, n) == 0; };
  } else {
   have 0 < n by { close(); }
   have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
   have to_integer(n - 1) < to_integer(n) by { close() using { 0 < n; }; }
   have defined(n - 1) by { close() using { 0 < n; }; }
   apply(ih(n - 1));
   apply(adler_sum_nonnegative(bytes, n));
   apply(adler_weighted_prefix_step(bytes, n));
   rewrite(adler_weighted_sum(bytes, n, n), adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n));
   close() using { 0 <= adler_weighted_sum(bytes, n - 1, n - 1); 0 <= adler_byte_sum(bytes, n); };
  }
 }
}

theorem adler_residue_unique(n: Integer, q: Integer, r: Integer) {
 requires 0 <= n;
 requires n == q * 65521 + r;
 requires 0 <= r;
 requires r <= 65520;
 ensures truncating_remainder(n, 65521) == r by {
  if q < 0 {
   have q <= -1 by { close() using { q < 0; }; }
   have n <= -1 by { close() using { n == q * 65521 + r; q <= -1; r <= 65520; }; }
   have not (0 <= n) by { close() using { n <= -1; }; }
   close();
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

theorem adler_residue_add(n: Integer, m: Integer) {
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
  apply(adler_residue_unique(n + m, truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521), truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)));
  close();
 }
}

function adler_spec_checksum(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 65536 * adler_spec_b(bytes, length, a0, b0) + adler_spec_a(bytes, length, a0)
}

theorem adler_spec_a_canonical(bytes: uint8[], n: int32, a0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 ensures 0 <= adler_spec_a(bytes, n, a0) and adler_spec_a(bytes, n, a0) <= 65520 by {
  apply(adler_sum_nonnegative(bytes, n));
  have 0 <= a0 + adler_byte_sum(bytes, n) by { close() using { 0 <= a0; 0 <= adler_byte_sum(bytes, n); }; }
  apply(integer::nonnegative_dividend_remainder(a0 + adler_byte_sum(bytes, n), 65521));
  apply(integer::positive_divisor_remainder_upper(a0 + adler_byte_sum(bytes, n), 65521));
  have truncating_remainder(a0 + adler_byte_sum(bytes, n), 65521) <= 65520 by { close() using { truncating_remainder(a0 + adler_byte_sum(bytes, n), 65521) <= 65521 - 1; }; }
  unfold(adler_spec_a(bytes, n, a0));
  all { 0 <= (truncating_remainder((to_integer(a0) + adler_byte_sum(bytes, n)), 65521) : Integer) => { close(); } (truncating_remainder((to_integer(a0) + adler_byte_sum(bytes, n)), 65521) : Integer) <= 65520 => { close(); } }
 }
}

theorem adler_spec_b_canonical(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_b(bytes, n, a0, b0) and adler_spec_b(bytes, n, a0, b0) <= 65520 by {
  apply(adler_weighted_nonnegative(bytes, n));
  have n <= 2147483647 by { close(); }
  have 0 <= to_integer(n) * a0 by {
   close() using { 0 <= to_integer(n); to_integer(n) <= 2147483647; 0 <= a0; a0 <= 65520; };
  }
  have 0 <= b0 + to_integer(n) * a0 by { close() using { 0 <= b0; 0 <= to_integer(n) * a0; }; }
  have 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n) by { close() using { 0 <= b0 + to_integer(n) * a0; 0 <= adler_weighted_sum(bytes, n, n); }; }
  apply(integer::nonnegative_dividend_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521));
  apply(integer::positive_divisor_remainder_upper(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521));
  have truncating_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521) <= 65520 by { close() using { truncating_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521) <= 65521 - 1; }; }
  unfold(adler_spec_b(bytes, n, a0, b0));
  all { 0 <= (truncating_remainder((to_integer(b0) + (to_integer(n) * to_integer(a0)) + adler_weighted_sum(bytes, n, n)), 65521) : Integer) => { close(); } (truncating_remainder((to_integer(b0) + (to_integer(n) * to_integer(a0)) + adler_weighted_sum(bytes, n, n)), 65521) : Integer) <= 65520 => { close(); } }
 }
}

theorem adler_spec_packing_bounds(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_checksum(bytes, n, a0, b0) and adler_spec_checksum(bytes, n, a0, b0) <= 4293984240 by {
  apply(adler_spec_a_canonical(bytes, n, a0));
  apply(adler_spec_b_canonical(bytes, n, a0, b0));
  unfold(adler_spec_checksum(bytes, n, a0, b0));
  all {
      0 <= (((65536 * adler_spec_b(bytes, n, a0, b0)) + adler_spec_a(bytes, n, a0)) : Integer) => {
          close() using { 0 <= adler_spec_b(bytes, n, a0, b0); 0 <= adler_spec_a(bytes, n, a0); };
      }
      (((65536 * adler_spec_b(bytes, n, a0, b0)) + adler_spec_a(bytes, n, a0)) : Integer) <= 4293984240 => {
          close() using { adler_spec_b(bytes, n, a0, b0) <= 65520; adler_spec_a(bytes, n, a0) <= 65520; };
      }
  }
 }
}

theorem adler_spec_empty(bytes: uint8[], a0: Integer, b0: Integer) {
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 requires b0 <= 65520;
 ensures adler_spec_a(bytes, 0, a0) == a0 by {
  apply(adler_sum_empty(bytes, 0));
  have a0 == 0 * 65521 + a0 by { close() using {}; }
  apply(adler_residue_unique(a0, 0, a0));
  unfold(adler_spec_a(bytes, 0, a0));
  rewrite(adler_byte_sum(bytes, 0), 0);
  close() using { truncating_remainder(a0, 65521) == a0; };
 }
 ensures adler_spec_b(bytes, 0, a0, b0) == b0 by {
  apply(adler_sum_empty(bytes, 0));
  have b0 == 0 * 65521 + b0 by { close() using {}; }
  apply(adler_residue_unique(b0, 0, b0));
  unfold(adler_spec_b(bytes, 0, a0, b0));
  rewrite(adler_weighted_sum(bytes, 0, 0), 0);
  have b0 + 0 * a0 + 0 == b0 by { close(); }
  rewrite(b0 + 0 * a0 + 0, b0);
  close();
 }
}

theorem adler_byte_observation_same_index(bytes: uint8[], i: int32, j: int32) {
 requires i == j;
 ensures to_integer(bytes[i] as int32) == to_integer(bytes[j] as int32) by { rewrite(i, j); close(); }
}

theorem adler_sum_append_four(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n <= 2147483643;
 ensures adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n) + to_integer(bytes[n] as int32) + to_integer(bytes[n + 1] as int32) + to_integer(bytes[n + 2] as int32) + to_integer(bytes[n + 3] as int32) by {
  have 0 < to_integer(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 1) - 1) == to_integer(n) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 1));
  have adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer(bytes[n] as int32) by { close() using { adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, (n + 1) - 1) + to_integer(bytes[(n + 1) - 1] as int32); to_integer((n + 1) - 1) == to_integer(n); }; }
  have 0 < to_integer(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 2) - 1) == to_integer(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 2));
  have to_integer(n + 1) == to_integer((n + 2) - 1) by { close() using { to_integer((n + 2) - 1) == to_integer(n + 1); }; }
  have adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer(bytes[n + 1] as int32) by { rewrite(to_integer(n + 1), to_integer((n + 2) - 1)); close(); }
  have 0 < to_integer(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 3) - 1) == to_integer(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 3));
  have to_integer(n + 2) == to_integer((n + 3) - 1) by { close() using { to_integer((n + 3) - 1) == to_integer(n + 2); }; }
  have adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer(bytes[n + 2] as int32) by { rewrite(to_integer(n + 2), to_integer((n + 3) - 1)); close(); }
  have 0 < to_integer(n + 4) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 4) - 1) == to_integer(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 4) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 4));
  have to_integer(n + 3) == to_integer((n + 4) - 1) by { close() using { to_integer((n + 4) - 1) == to_integer(n + 3); }; }
  have adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer(bytes[n + 3] as int32) by { rewrite(to_integer(n + 3), to_integer((n + 4) - 1)); close(); }
  rewrite(adler_byte_sum(bytes, n + 4), adler_byte_sum(bytes, n + 3) + to_integer(bytes[n + 3] as int32));
  rewrite(adler_byte_sum(bytes, n + 3), adler_byte_sum(bytes, n + 2) + to_integer(bytes[n + 2] as int32));
  rewrite(adler_byte_sum(bytes, n + 2), adler_byte_sum(bytes, n + 1) + to_integer(bytes[n + 1] as int32));
  rewrite(adler_byte_sum(bytes, n + 1), adler_byte_sum(bytes, n) + to_integer(bytes[n] as int32));
  close() using {};
 }
}

theorem adler_weighted_append_four(bytes: uint8[], n: int32) {
 requires 0 <= n;
 requires n <= 2147483643;
 ensures adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n, n) + 4 * adler_byte_sum(bytes, n) + 4 * to_integer(bytes[n] as int32) + 3 * to_integer(bytes[n + 1] as int32) + 2 * to_integer(bytes[n + 2] as int32) + to_integer(bytes[n + 3] as int32) by {
  have 0 < to_integer(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 1) - 1) == to_integer(n) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 1));
  have adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + to_integer(bytes[n] as int32) by { close() using { adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, (n + 1) - 1) + to_integer(bytes[(n + 1) - 1] as int32); to_integer((n + 1) - 1) == to_integer(n); }; }
  have 0 < to_integer(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 2) - 1) == to_integer(n + 1) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 2));
  have to_integer(n + 1) == to_integer((n + 2) - 1) by { close() using { to_integer((n + 2) - 1) == to_integer(n + 1); }; }
  have adler_byte_sum(bytes, n + 2) == adler_byte_sum(bytes, n + 1) + to_integer(bytes[n + 1] as int32) by { rewrite(to_integer(n + 1), to_integer((n + 2) - 1)); close(); }
  have 0 < to_integer(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 3) - 1) == to_integer(n + 2) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 3));
  have to_integer(n + 2) == to_integer((n + 3) - 1) by { close() using { to_integer((n + 3) - 1) == to_integer(n + 2); }; }
  have adler_byte_sum(bytes, n + 3) == adler_byte_sum(bytes, n + 2) + to_integer(bytes[n + 2] as int32) by { rewrite(to_integer(n + 2), to_integer((n + 3) - 1)); close(); }
  have 0 < to_integer(n + 4) by { close() using { 0 <= n; n <= 2147483643; }; }
  have to_integer((n + 4) - 1) == to_integer(n + 3) by { close() using { 0 <= n; n <= 2147483643; }; }
  have defined(n + 4) by { close() using { 0 <= n; n <= 2147483643; }; }
  apply(adler_sum_append(bytes, n + 4));
  have to_integer(n + 3) == to_integer((n + 4) - 1) by { close() using { to_integer((n + 4) - 1) == to_integer(n + 3); }; }
  have adler_byte_sum(bytes, n + 4) == adler_byte_sum(bytes, n + 3) + to_integer(bytes[n + 3] as int32) by { rewrite(to_integer(n + 3), to_integer((n + 4) - 1)); close(); }
  apply(adler_weighted_prefix_step(bytes, n + 1));
  have adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1) by { close() using { adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, (n + 1) - 1, (n + 1) - 1) + adler_byte_sum(bytes, n + 1); to_integer((n + 1) - 1) == to_integer(n); }; }
  apply(adler_weighted_prefix_step(bytes, n + 2));
  have adler_weighted_sum(bytes, n + 2, n + 2) == adler_weighted_sum(bytes, n + 1, n + 1) + adler_byte_sum(bytes, n + 2) by { rewrite(to_integer(n + 1), to_integer((n + 2) - 1)); close(); }
  apply(adler_weighted_prefix_step(bytes, n + 3));
  have adler_weighted_sum(bytes, n + 3, n + 3) == adler_weighted_sum(bytes, n + 2, n + 2) + adler_byte_sum(bytes, n + 3) by { rewrite(to_integer(n + 2), to_integer((n + 3) - 1)); close(); }
  apply(adler_weighted_prefix_step(bytes, n + 4));
  have adler_weighted_sum(bytes, n + 4, n + 4) == adler_weighted_sum(bytes, n + 3, n + 3) + adler_byte_sum(bytes, n + 4) by { rewrite(to_integer(n + 3), to_integer((n + 4) - 1)); close(); }
  rewrite(adler_weighted_sum(bytes, n + 4, n + 4), adler_weighted_sum(bytes, n + 3, n + 3) + adler_byte_sum(bytes, n + 4));
  rewrite(adler_weighted_sum(bytes, n + 3, n + 3), adler_weighted_sum(bytes, n + 2, n + 2) + adler_byte_sum(bytes, n + 3));
  rewrite(adler_weighted_sum(bytes, n + 2, n + 2), adler_weighted_sum(bytes, n + 1, n + 1) + adler_byte_sum(bytes, n + 2));
  rewrite(adler_weighted_sum(bytes, n + 1, n + 1), adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1));
  rewrite(adler_byte_sum(bytes, n + 4), adler_byte_sum(bytes, n + 3) + to_integer(bytes[n + 3] as int32));
  rewrite(adler_byte_sum(bytes, n + 3), adler_byte_sum(bytes, n + 2) + to_integer(bytes[n + 2] as int32));
  rewrite(adler_byte_sum(bytes, n + 2), adler_byte_sum(bytes, n + 1) + to_integer(bytes[n + 1] as int32));
  rewrite(adler_byte_sum(bytes, n + 1), adler_byte_sum(bytes, n) + to_integer(bytes[n] as int32));
  close() using {};
 }
}

// A signed quotient difference can witness congruence even when either
// representative is smaller. Both dividend interpretations remain nonnegative.
theorem adler_residue_congruent(n: Integer, m: Integer, q: Integer) {
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
  apply(adler_residue_unique(n, truncating_quotient(m, 65521) + q, truncating_remainder(m, 65521)));
  close();
 }
}

theorem adler_spec_one(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 1, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 1));
  apply(adler_sum_append(bytes, 1));
  unfold(adler_spec_a(bytes, 1, 1));
  rewrite(adler_byte_sum(bytes, 1), adler_byte_sum(bytes, 0) + to_integer(bytes[0] as int32));
  rewrite(adler_byte_sum(bytes, 0), 0);
  close();
 }
 ensures adler_spec_b(bytes, 1, 1, 0) == truncating_remainder(1 + to_integer(bytes[0] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 1));
  apply(adler_weighted_append(bytes, 1, 1));
  unfold(adler_spec_b(bytes, 1, 1, 0));
  have adler_weighted_sum(bytes, 1, 1) == adler_weighted_sum(bytes, 0, 1) + to_integer(bytes[0] as int32) by { close() using { adler_weighted_sum(bytes, 1, 1) == adler_weighted_sum(bytes, 0, 1) + (1 - 0) * to_integer(bytes[0] as int32); }; }
  rewrite(adler_weighted_sum(bytes, 1, 1), adler_weighted_sum(bytes, 0, 1) + to_integer(bytes[0] as int32));
  rewrite(adler_weighted_sum(bytes, 0, 1), 0);
  close();
 }
}

theorem adler_byte_offset_association(bytes: uint8[], prefix: int32, suffix: int32) {
 requires defined(prefix + suffix);
 ensures to_integer((bytes + prefix)[suffix] as int32) == to_integer(bytes[prefix + suffix] as int32) by {
  have (bytes + prefix) + suffix == bytes + (prefix + suffix) by { close() using { defined(prefix + suffix); }; }
  have (bytes + prefix)[suffix] as int32 == bytes[prefix + suffix] as int32 by {
   rewrite((bytes + prefix) + suffix, bytes + (prefix + suffix)); close();
  }
  rewrite((bytes + prefix)[suffix] as int32, bytes[prefix + suffix] as int32); close();
 }
}

theorem adler_sum_concat(bytes: uint8[], prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 ensures adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix) by {
  let ih = induct(suffix);
  if suffix <= 0 {
   have suffix == 0 by { close() using { 0 <= suffix; suffix <= 0; }; }
   have to_integer(prefix + suffix) == to_integer(prefix) by {
    apply(integer::int32_add_to_integer(prefix, suffix));
    rewrite(to_integer(prefix + suffix), to_integer(prefix) + to_integer(suffix));
    rewrite(suffix, 0);
    close();
   }
   apply(adler_sum_empty(bytes + prefix, 0));
   have adler_byte_sum(bytes + prefix, suffix) == 0 by { rewrite(suffix, 0); close(); }
   rewrite(to_integer(prefix + suffix), to_integer(prefix));
   close() using { adler_byte_sum(bytes + prefix, suffix) == 0; };
  } else {
   have 0 < suffix by { close(); }
   have 0 <= to_integer(suffix - 1) by { close() using { 0 < suffix; }; }
   have to_integer(suffix - 1) < to_integer(suffix) by { close() using { 0 < suffix; }; }
   have 1 <= suffix by { close() using { 0 < suffix; }; }
   have defined(suffix - 1);
   have defined(suffix - 1) by { close(); }
   have suffix <= 2147483647 by { close(); }
   have to_integer(suffix - 1) <= 2147483647 by { close(); }
   have defined(2147483647 - suffix);
   have defined(2147483647 - (suffix - 1));
   have defined(2147483647 - suffix) by { close(); }
   have defined(2147483647 - (suffix - 1)) by { close(); }
   have to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
   have to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
   have to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { close() using {
    to_integer(prefix) <= to_integer(2147483647 - suffix);
    to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
    to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   }; }
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { close(); }
   have defined(prefix + (suffix - 1));
   have defined(prefix + (suffix - 1)) by { close(); }
   apply(ih(suffix - 1));
   have 0 < to_integer(prefix + suffix) by { close() using { 0 <= prefix; 0 <= suffix; 0 < suffix; to_integer(prefix) <= to_integer(2147483647 - suffix); suffix <= 2147483647; defined(prefix + suffix); defined(suffix - 1); 0 <= to_integer(suffix - 1); defined(2147483647 - suffix); defined(2147483647 - (suffix - 1)); }; }
   have 1 <= to_integer(prefix + suffix) by { close() using { 0 <= prefix; 0 <= suffix; 0 < suffix; to_integer(prefix) <= to_integer(2147483647 - suffix); suffix <= 2147483647; defined(prefix + suffix); defined(2147483647 - suffix); }; }
   have defined((prefix + suffix) - 1);
   have defined((prefix + suffix) - 1) by { close(); }
   have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   have to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   }; }
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { close(); }
   apply(adler_sum_append(bytes, prefix + suffix));
   apply(adler_sum_append(bytes + prefix, suffix));
   apply(adler_byte_offset_association(bytes, prefix, suffix - 1));
   have adler_byte_sum(bytes, (prefix + suffix) - 1) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix - 1) by {
    rewrite(to_integer((prefix + suffix) - 1), to_integer(prefix + (suffix - 1))); close();
   }
   have to_integer(bytes[(prefix + suffix) - 1] as int32) == to_integer((bytes + prefix)[suffix - 1] as int32) by {
    rewrite(to_integer((prefix + suffix) - 1), to_integer(prefix + (suffix - 1))); rewrite(to_integer((bytes + prefix)[suffix - 1] as int32), to_integer(bytes[prefix + (suffix - 1)] as int32)); close();
   }
   close() using {
    adler_byte_sum(bytes, prefix + suffix) == adler_byte_sum(bytes, (prefix + suffix) - 1) + to_integer(bytes[(prefix + suffix) - 1] as int32);
    adler_byte_sum(bytes + prefix, suffix) == adler_byte_sum(bytes + prefix, suffix - 1) + to_integer((bytes + prefix)[suffix - 1] as int32);
    adler_byte_sum(bytes, (prefix + suffix) - 1) == adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix - 1);
    to_integer(bytes[(prefix + suffix) - 1] as int32) == to_integer((bytes + prefix)[suffix - 1] as int32);
   };
  }
 }
}

theorem adler_weighted_concat(bytes: uint8[], prefix: int32, suffix: int32, weight_end: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 requires defined(weight_end - prefix);
 ensures adler_weighted_sum(bytes, prefix + suffix, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) by {
  let ih = induct(suffix);
  have to_integer(weight_end - prefix) == to_integer(weight_end) - to_integer(prefix);
  if suffix <= 0 {
   have suffix == 0 by { close() using { 0 <= suffix; suffix <= 0; }; }
   have to_integer(prefix + suffix) == to_integer(prefix) by {
    apply(integer::int32_add_to_integer(prefix, suffix));
    rewrite(to_integer(prefix + suffix), to_integer(prefix) + to_integer(suffix));
    rewrite(suffix, 0);
    close();
   }
   apply(adler_sum_empty(bytes + prefix, weight_end - prefix));
   have adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == 0 by { rewrite(suffix, 0); close(); }
   rewrite(to_integer(prefix + suffix), to_integer(prefix));
   close() using { adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == 0; };
  } else {
   have 0 < suffix by { close(); }
   have 0 <= to_integer(suffix - 1) by { close() using { 0 < suffix; }; }
   have to_integer(suffix - 1) < to_integer(suffix) by { close() using { 0 < suffix; }; }
   have 1 <= suffix by { close() using { 0 < suffix; }; }
   have defined(suffix - 1);
   have defined(suffix - 1) by { close(); }
   have suffix <= 2147483647 by { close(); }
   have to_integer(suffix - 1) <= 2147483647 by { close(); }
   have defined(2147483647 - suffix);
   have defined(2147483647 - (suffix - 1));
   have defined(2147483647 - suffix) by { close(); }
   have defined(2147483647 - (suffix - 1)) by { close(); }
   have to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
   have to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
   have to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { close() using {
    to_integer(prefix) <= to_integer(2147483647 - suffix);
    to_integer(2147483647 - suffix) == to_integer(2147483647) - to_integer(suffix);
    to_integer(2147483647 - (suffix - 1)) == to_integer(2147483647) - to_integer(suffix - 1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   }; }
   have to_integer(prefix) <= to_integer(2147483647 - (suffix - 1)) by { close(); }
   have defined(prefix + (suffix - 1));
   have defined(prefix + (suffix - 1)) by { close(); }
   apply(ih(suffix - 1));
   have 0 < to_integer(prefix + suffix) by { close() using { 0 <= prefix; 0 <= suffix; 0 < suffix; to_integer(prefix) <= to_integer(2147483647 - suffix); suffix <= 2147483647; defined(prefix + suffix); defined(suffix - 1); 0 <= to_integer(suffix - 1); defined(2147483647 - suffix); defined(2147483647 - (suffix - 1)); }; }
   have 1 <= to_integer(prefix + suffix) by { close() using { 0 <= prefix; 0 <= suffix; 0 < suffix; to_integer(prefix) <= to_integer(2147483647 - suffix); suffix <= 2147483647; defined(prefix + suffix); defined(2147483647 - suffix); }; }
   have defined((prefix + suffix) - 1);
   have defined((prefix + suffix) - 1) by { close(); }
   have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   have to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { close() using {
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer(prefix + (suffix - 1)) == to_integer(prefix) + to_integer(suffix - 1);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   }; }
   have to_integer((prefix + suffix) - 1) == to_integer(prefix + (suffix - 1)) by { close(); }
   apply(adler_weighted_append(bytes, prefix + suffix, weight_end));
   apply(adler_weighted_append(bytes + prefix, suffix, weight_end - prefix));
   apply(adler_byte_offset_association(bytes, prefix, suffix - 1));
   have adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix) by {
    rewrite(to_integer((prefix + suffix) - 1), to_integer(prefix + (suffix - 1))); close();
   }
   have to_integer(bytes[(prefix + suffix) - 1] as int32) == to_integer((bytes + prefix)[suffix - 1] as int32) by {
    rewrite(to_integer((prefix + suffix) - 1), to_integer(prefix + (suffix - 1))); rewrite(to_integer((bytes + prefix)[suffix - 1] as int32), to_integer(bytes[prefix + (suffix - 1)] as int32)); close();
   }
   have to_integer(weight_end) - to_integer((prefix + suffix) - 1) == to_integer(weight_end - prefix) - to_integer(suffix - 1) by { close() using {
    to_integer(weight_end - prefix) == to_integer(weight_end) - to_integer(prefix);
    to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
    to_integer((prefix + suffix) - 1) == to_integer(prefix + suffix) - to_integer(1);
    to_integer(suffix - 1) == to_integer(suffix) - to_integer(1);
   }; }
   have (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer(bytes[(prefix + suffix) - 1] as int32) == (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((bytes + prefix)[suffix - 1] as int32) by {
    rewrite(to_integer(weight_end) - to_integer((prefix + suffix) - 1), to_integer(weight_end - prefix) - to_integer(suffix - 1));
    rewrite(to_integer(bytes[(prefix + suffix) - 1] as int32), to_integer((bytes + prefix)[suffix - 1] as int32));
    close();
   }
   close() using {
    adler_weighted_sum(bytes, prefix + suffix, weight_end) == adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) + (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer(bytes[(prefix + suffix) - 1] as int32);
    adler_weighted_sum(bytes + prefix, suffix, weight_end - prefix) == adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix) + (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((bytes + prefix)[suffix - 1] as int32);
    adler_weighted_sum(bytes, (prefix + suffix) - 1, weight_end) == adler_weighted_sum(bytes, prefix, weight_end) + adler_weighted_sum(bytes + prefix, suffix - 1, weight_end - prefix);
    to_integer(bytes[(prefix + suffix) - 1] as int32) == to_integer((bytes + prefix)[suffix - 1] as int32);
    to_integer(weight_end) - to_integer((prefix + suffix) - 1) == to_integer(weight_end - prefix) - to_integer(suffix - 1);
    (to_integer(weight_end) - to_integer((prefix + suffix) - 1)) * to_integer(bytes[(prefix + suffix) - 1] as int32) == (to_integer(weight_end - prefix) - to_integer(suffix - 1)) * to_integer((bytes + prefix)[suffix - 1] as int32);
   };
  }
 }
}

theorem adler_residue_add_left(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + m, 65521) by {
  apply(integer::truncation_identity(n, 65521));
  apply(integer::nonnegative_dividend_remainder(n, 65521));
  have 0 <= n + m by { close() using { 0 <= n; 0 <= m; }; }
  have 0 <= truncating_remainder(n, 65521) + m by { close() using { 0 <= truncating_remainder(n, 65521); 0 <= m; }; }
  have n + m == (truncating_remainder(n, 65521) + m) + 65521 * truncating_quotient(n, 65521) by { close() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); }; }
  apply(adler_residue_congruent(n + m, truncating_remainder(n, 65521) + m, truncating_quotient(n, 65521)));
  close();
 }
}

theorem adler_spec_a_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 requires 0 <= a0;
 ensures adler_spec_a(bytes, prefix + suffix, a0) == adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)) by {
  apply(adler_sum_concat(bytes, prefix, suffix));
  apply(adler_sum_nonnegative(bytes, prefix));
  apply(adler_sum_nonnegative(bytes + prefix, suffix));
  have 0 <= a0 + adler_byte_sum(bytes, prefix) by { close() using { 0 <= a0; 0 <= adler_byte_sum(bytes, prefix); }; }
  apply(adler_residue_add_left(a0 + adler_byte_sum(bytes, prefix), adler_byte_sum(bytes + prefix, suffix)));
  unfold(adler_spec_a(bytes, prefix + suffix, a0));
  unfold(adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)));
  unfold(adler_spec_a(bytes, prefix, a0));
  rewrite(adler_byte_sum(bytes, prefix + suffix), adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix));
  have a0 + (adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix)) == (a0 + adler_byte_sum(bytes, prefix)) + adler_byte_sum(bytes + prefix, suffix) by { close() using {}; }
  rewrite(a0 + (adler_byte_sum(bytes, prefix) + adler_byte_sum(bytes + prefix, suffix)), (a0 + adler_byte_sum(bytes, prefix)) + adler_byte_sum(bytes + prefix, suffix));
  close();
 }
}

theorem adler_sum_upper(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures adler_byte_sum(bytes, n) <= 255 * to_integer(n) by {
  let ih = induct(n);
  if n <= 0 {
   have n == 0 by { close() using { 0 <= n; n <= 0; }; }
   apply(adler_sum_empty(bytes, 0));
   rewrite(n, 0);
   close() using { adler_byte_sum(bytes, 0) == 0; };
  } else {
   have 0 < n by { close(); }
   have 0 <= to_integer(n - 1) by { close() using { 0 < n; }; }
   have to_integer(n - 1) < to_integer(n) by { close() using { 0 < n; }; }
   have defined(n - 1) by { close() using { 0 < n; }; }
   apply(ih(n - 1));
   apply(adler_sum_append(bytes, n));
   apply(adler_byte_bounds(bytes[n - 1]));
   have to_integer(n - 1) == to_integer(n) - to_integer(1);
   close() using {
    adler_byte_sum(bytes, n - 1) <= 255 * to_integer(n - 1);
    adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer(bytes[n - 1] as int32);
    to_integer(bytes[n - 1] as int32) <= 255;
    to_integer(n - 1) == to_integer(n) - to_integer(1);
   };
  }
 }
}

theorem adler_seed_polynomial(x: Integer, y: Integer, k: Integer, z: Integer, qa: Integer, ra: Integer, qb: Integer, rb: Integer) {
 requires x == qa * 65521 + ra;
 requires y == qb * 65521 + rb;
 ensures y + k * x + z == (rb + k * ra + z) + 65521 * (qb + k * qa) by {
  rewrite(y, qb * 65521 + rb);
  rewrite(x, qa * 65521 + ra);
  close() using {  };
 }
}

theorem adler_residue_seed_update(x: Integer, y: Integer, k: Integer, z: Integer) {
 requires 0 <= x;
 requires x <= 549755879424;
 requires 0 <= y;
 requires 0 <= k;
 requires k <= 2147483647;
 requires 0 <= z;
 ensures truncating_remainder(y + k * x + z, 65521) == truncating_remainder(truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, 65521) by {
  apply(integer::truncation_identity(x, 65521));
  apply(integer::truncation_identity(y, 65521));
  apply(integer::nonnegative_dividend_remainder(x, 65521));
  apply(integer::nonnegative_dividend_remainder(y, 65521));
  apply(integer::positive_divisor_remainder_upper(x, 65521));
  have truncating_remainder(x, 65521) <= 65520 by { close() using { truncating_remainder(x, 65521) <= 65521 - 1; }; }
  have 0 <= k * x by { close() using { 0 <= k; k <= 2147483647; 0 <= x; x <= 549755879424; }; }
  have 0 <= k * truncating_remainder(x, 65521) by { close() using { 0 <= k; k <= 2147483647; 0 <= truncating_remainder(x, 65521); truncating_remainder(x, 65521) <= 65520; }; }
  have 0 <= y + k * x + z by { close() using { 0 <= y; 0 <= k * x; 0 <= z; }; }
  have 0 <= truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z by { close() using { 0 <= truncating_remainder(y, 65521); 0 <= k * truncating_remainder(x, 65521); 0 <= z; }; }
  apply(adler_seed_polynomial(x, y, k, z, truncating_quotient(x, 65521), truncating_remainder(x, 65521), truncating_quotient(y, 65521), truncating_remainder(y, 65521)));
  apply(adler_residue_congruent(y + k * x + z, truncating_remainder(y, 65521) + k * truncating_remainder(x, 65521) + z, truncating_quotient(y, 65521) + k * truncating_quotient(x, 65521)));
  close();
 }
}

// The definedness facts, stated apart so the observations of
// `adler_concat_index_partition` are stated where these are established.
theorem adler_concat_index_partition_defined(prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 ensures defined((prefix + suffix) - prefix) by {
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have to_integer(prefix) <= to_integer(prefix + suffix) by { close() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
   to_integer(0) <= to_integer(suffix);
  }; }
  have to_integer(prefix) <= to_integer(prefix + suffix) by { close(); }
  have defined((prefix + suffix) - prefix);
  close();
 }
}

theorem adler_concat_index_partition(prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 requires defined((prefix + suffix) - prefix);
 ensures defined((prefix + suffix) - prefix) by { close(); }
 ensures to_integer((prefix + suffix) - prefix) == to_integer(suffix) by {
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
  close() using {
   to_integer((prefix + suffix) - prefix) == to_integer(prefix + suffix) - to_integer(prefix);
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  };
 }
}

theorem adler_weighted_prefix_concat(bytes: uint8[], prefix: int32, suffix: int32) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 ensures adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix) by {
  apply(adler_concat_index_partition_defined(prefix, suffix)); apply(adler_concat_index_partition(prefix, suffix));
  have defined((prefix + suffix) - prefix) by { close(); }
  have to_integer((prefix + suffix) - prefix) == to_integer(suffix) by { close(); }
  apply(adler_weighted_concat(bytes, prefix, suffix, prefix + suffix));
  have adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix + suffix) + adler_weighted_sum(bytes + prefix, suffix, suffix) by {
   rewrite(to_integer(suffix), to_integer((prefix + suffix) - prefix));
   close();
  }
  apply(adler_weight_shift(bytes, prefix, prefix, prefix + suffix));
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  have to_integer(prefix + suffix) - to_integer(prefix) == to_integer(suffix) by { close() using {
   to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  }; }
  have adler_weighted_sum(bytes, prefix, prefix + suffix) - adler_weighted_sum(bytes, prefix, prefix) == to_integer(suffix) * adler_byte_sum(bytes, prefix) by {
   rewrite(to_integer(suffix), to_integer(prefix + suffix) - to_integer(prefix));
   close();
  }
  close() using {
   adler_weighted_sum(bytes, prefix + suffix, prefix + suffix) == adler_weighted_sum(bytes, prefix, prefix + suffix) + adler_weighted_sum(bytes + prefix, suffix, suffix);
   adler_weighted_sum(bytes, prefix, prefix + suffix) - adler_weighted_sum(bytes, prefix, prefix) == to_integer(suffix) * adler_byte_sum(bytes, prefix);
  };
 }
}

theorem adler_join_seed_polynomial(a0: Integer, b0: Integer, p: Integer, s: Integer, sp: Integer, wp: Integer, wt: Integer) {
 ensures b0 + (p + s) * a0 + (wp + s * sp + wt) == (b0 + p * a0 + wp) + s * (a0 + sp) + wt by {
  close() using {  };
 }
}

theorem adler_spec_b_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer, b0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_b(bytes, prefix + suffix, a0, b0) == adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by {
  apply(adler_weighted_prefix_concat(bytes, prefix, suffix));
  apply(adler_sum_nonnegative(bytes, prefix));
  apply(adler_sum_upper(bytes, prefix));
  apply(adler_weighted_nonnegative(bytes, prefix));
  apply(adler_weighted_nonnegative(bytes + prefix, suffix));
  have prefix <= 2147483647 by { close(); }
  have suffix <= 2147483647 by { close(); }
  have 0 <= to_integer(prefix) by { close() using { to_integer(0) <= to_integer(prefix); }; }
  have to_integer(prefix) <= 2147483647 by { close() using { to_integer(prefix) <= to_integer(2147483647); }; }
  have 0 <= to_integer(prefix) * a0 by { close() using { 0 <= to_integer(prefix); to_integer(prefix) <= 2147483647; 0 <= a0; a0 <= 65520; }; }
  have 0 <= a0 + adler_byte_sum(bytes, prefix) by { close() using { 0 <= a0; 0 <= adler_byte_sum(bytes, prefix); }; }
  have 255 * to_integer(prefix) <= 547608329985 by { close() using { to_integer(prefix) <= 2147483647; }; }
  have adler_byte_sum(bytes, prefix) <= 547608329985 by { close() using {
   adler_byte_sum(bytes, prefix) <= 255 * to_integer(prefix);
   255 * to_integer(prefix) <= 547608329985;
  }; }
  have a0 + adler_byte_sum(bytes, prefix) <= 549755879424 by { close() using {
   a0 <= 65520; adler_byte_sum(bytes, prefix) <= 547608329985;
  }; }
  have 0 <= b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix) by { close() using { 0 <= b0; 0 <= to_integer(prefix) * a0; 0 <= adler_weighted_sum(bytes, prefix, prefix); }; }
  have 0 <= to_integer(suffix) by { close() using { to_integer(0) <= to_integer(suffix); }; }
  have to_integer(suffix) <= 2147483647 by { close() using { to_integer(suffix) <= to_integer(2147483647); }; }
  apply(adler_residue_seed_update(a0 + adler_byte_sum(bytes, prefix), b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix), to_integer(suffix), adler_weighted_sum(bytes + prefix, suffix, suffix)));
  have to_integer(prefix + suffix) == to_integer(prefix) + to_integer(suffix);
  apply(adler_join_seed_polynomial(a0, b0, to_integer(prefix), to_integer(suffix), adler_byte_sum(bytes, prefix), adler_weighted_sum(bytes, prefix, prefix), adler_weighted_sum(bytes + prefix, suffix, suffix)));
  unfold(adler_spec_b(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  unfold(adler_spec_a(bytes, prefix, a0));
  unfold(adler_spec_b(bytes, prefix, a0, b0));
  rewrite(adler_weighted_sum(bytes, prefix + suffix, prefix + suffix), adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix));
  rewrite(to_integer(prefix + suffix), to_integer(prefix) + to_integer(suffix));
  rewrite(b0 + (to_integer(prefix) + to_integer(suffix)) * a0 + (adler_weighted_sum(bytes, prefix, prefix) + to_integer(suffix) * adler_byte_sum(bytes, prefix) + adler_weighted_sum(bytes + prefix, suffix, suffix)), (b0 + to_integer(prefix) * a0 + adler_weighted_sum(bytes, prefix, prefix)) + to_integer(suffix) * (a0 + adler_byte_sum(bytes, prefix)) + adler_weighted_sum(bytes + prefix, suffix, suffix));
  close();
 }
}

theorem adler_spec_checksum_concat(bytes: uint8[], prefix: int32, suffix: int32, a0: Integer, b0: Integer) {
 requires 0 <= prefix;
 requires 0 <= suffix;
 requires to_integer(prefix) <= to_integer(2147483647 - suffix);
 requires defined(prefix + suffix);
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures adler_spec_checksum(bytes, prefix + suffix, a0, b0) == adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)) by {
  apply(adler_spec_a_concat(bytes, prefix, suffix, a0));
  apply(adler_spec_b_concat(bytes, prefix, suffix, a0, b0));
  unfold(adler_spec_checksum(bytes, prefix + suffix, a0, b0));
  unfold(adler_spec_checksum(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  rewrite(adler_spec_a(bytes, prefix + suffix, a0), adler_spec_a(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0)));
  rewrite(adler_spec_b(bytes, prefix + suffix, a0, b0), adler_spec_b(bytes + prefix, suffix, adler_spec_a(bytes, prefix, a0), adler_spec_b(bytes, prefix, a0, b0)));
  close();
 }
}

theorem adler_spec_four(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 4, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 0));
  apply(adler_sum_append_four(bytes, 0));
  have 1 + (0 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)) == 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32) by { close() using {}; }
  unfold(adler_spec_a(bytes, 4, 1));
  rewrite(adler_byte_sum(bytes, 4), adler_byte_sum(bytes, 0) + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32));
  rewrite(adler_byte_sum(bytes, 0), 0);
  rewrite(1 + (0 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)), 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)); close();
 }
 ensures adler_spec_b(bytes, 4, 1, 0) == truncating_remainder(4 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 0));
  apply(adler_weighted_append_four(bytes, 0));
  have 0 + 4 * 1 + (0 + 4 * 0 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)) == 4 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32) by { close() using {}; }
  unfold(adler_spec_b(bytes, 4, 1, 0));
  rewrite(adler_weighted_sum(bytes, 4, 4), adler_weighted_sum(bytes, 0, 0) + 4 * adler_byte_sum(bytes, 0) + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32));
  rewrite(adler_weighted_sum(bytes, 0, 0), 0);
  rewrite(adler_byte_sum(bytes, 0), 0);
  rewrite(0 + 4 * 1 + (0 + 4 * 0 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)), 4 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32)); close();
 }
}

theorem adler_spec_two(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 2, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 2));
  apply(adler_sum_append(bytes, 1));
  apply(adler_sum_append(bytes, 2));
  have adler_byte_sum(bytes, 2) == to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) by { close() using { adler_byte_sum(bytes, 0) == 0; adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + to_integer(bytes[0] as int32); adler_byte_sum(bytes, 2) == adler_byte_sum(bytes, 1) + to_integer(bytes[1] as int32); }; }
  have 1 + (to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32)) == 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) by { close() using {}; }
  unfold(adler_spec_a(bytes, 2, 1));
  rewrite(adler_byte_sum(bytes, 2), to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32));
  rewrite(1 + (to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32)), 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32));
  close();
 }
 ensures adler_spec_b(bytes, 2, 1, 0) == truncating_remainder(2 + 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 2));
  apply(adler_weighted_append(bytes, 1, 2));
  apply(adler_weighted_append(bytes, 2, 2));
  have adler_weighted_sum(bytes, 2, 2) == 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) by { close() using { adler_weighted_sum(bytes, 0, 2) == 0; adler_weighted_sum(bytes, 1, 2) == adler_weighted_sum(bytes, 0, 2) + (2 - 0) * to_integer(bytes[0] as int32); adler_weighted_sum(bytes, 2, 2) == adler_weighted_sum(bytes, 1, 2) + (2 - 1) * to_integer(bytes[1] as int32); }; }
  have 0 + 2 * 1 + (2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32)) == 2 + 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) by { close() using {}; }
  unfold(adler_spec_b(bytes, 2, 1, 0));
  rewrite(adler_weighted_sum(bytes, 2, 2), 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32));
  rewrite(0 + 2 * 1 + (2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32)), 2 + 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32));
  close();
 }
}

theorem adler_spec_three(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 3, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 3));
  apply(adler_sum_append(bytes, 1));
  apply(adler_sum_append(bytes, 2));
  apply(adler_sum_append(bytes, 3));
  have adler_byte_sum(bytes, 3) == to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) by { close() using { adler_byte_sum(bytes, 0) == 0; adler_byte_sum(bytes, 1) == adler_byte_sum(bytes, 0) + to_integer(bytes[0] as int32); adler_byte_sum(bytes, 2) == adler_byte_sum(bytes, 1) + to_integer(bytes[1] as int32); adler_byte_sum(bytes, 3) == adler_byte_sum(bytes, 2) + to_integer(bytes[2] as int32); }; }
  have 1 + (to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32)) == 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) by { close() using {}; }
  unfold(adler_spec_a(bytes, 3, 1));
  rewrite(adler_byte_sum(bytes, 3), to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32));
  rewrite(1 + (to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32)), 1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32));
  close();
 }
 ensures adler_spec_b(bytes, 3, 1, 0) == truncating_remainder(3 + 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32), 65521) by {
  apply(adler_sum_empty(bytes, 3));
  apply(adler_weighted_append(bytes, 1, 3));
  apply(adler_weighted_append(bytes, 2, 3));
  apply(adler_weighted_append(bytes, 3, 3));
  have adler_weighted_sum(bytes, 3, 3) == 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) by { close() using { adler_weighted_sum(bytes, 0, 3) == 0; adler_weighted_sum(bytes, 1, 3) == adler_weighted_sum(bytes, 0, 3) + (3 - 0) * to_integer(bytes[0] as int32); adler_weighted_sum(bytes, 2, 3) == adler_weighted_sum(bytes, 1, 3) + (3 - 1) * to_integer(bytes[1] as int32); adler_weighted_sum(bytes, 3, 3) == adler_weighted_sum(bytes, 2, 3) + (3 - 2) * to_integer(bytes[2] as int32); }; }
  have 0 + 3 * 1 + (3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32)) == 3 + 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) by { close() using {}; }
  unfold(adler_spec_b(bytes, 3, 1, 0));
  rewrite(adler_weighted_sum(bytes, 3, 3), 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32));
  rewrite(0 + 3 * 1 + (3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32)), 3 + 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32));
  close();
 }
}

// Extensionality uses only equality of the selected input bytes; it grants no memory authority.
theorem adler_sums_extensional(left: uint8[], right: uint8[], bound: int32, n: int32, weight: int32) {
 requires 0 <= n;
 requires n <= bound;
 requires forall (k: int32) { 0 <= k and k < bound implies left[k] == right[k] };
 ensures adler_byte_sum(left, n) == adler_byte_sum(right, n) and adler_weighted_sum(left, n, weight) == adler_weighted_sum(right, n, weight) by {
  let ih = induct(n);
  if n <= 0 {
   apply(adler_sum_empty(left, weight));
   apply(adler_sum_empty(right, weight));
   have n == 0 by close() using { 0 <= n; n <= 0; };
   rewrite(n, 0);
   rewrite(adler_byte_sum(left, 0), 0);
   rewrite(adler_byte_sum(right, 0), 0);
   rewrite(adler_weighted_sum(left, 0, weight), 0);
   rewrite(adler_weighted_sum(right, 0, weight), 0);
   all { (0 : Integer) == 0 => { close(); } (0 : Integer) == 0 => { close(); } }
  } else {
   have 0 < n;
   have 0 <= to_integer(n - 1) by close() using { 0 < n; };
   have to_integer(n - 1) < to_integer(n) by close() using { 0 < n; };
   have to_integer(n - 1) <= to_integer(bound) by close() using { n <= bound; 0 < n; };
   have to_integer(n - 1) < to_integer(bound) by close() using { n <= bound; 0 < n; };
   apply(ih(n - 1));
   have 0 <= (n - 1) and (n - 1) < bound;
   instantiate(forall (k: int32) { 0 <= k and k < bound implies left[k] == right[k] }, n - 1);
   apply(adler_sum_append(left, n));
   apply(adler_sum_append(right, n));
   apply(adler_weighted_append(left, n, weight));
   apply(adler_weighted_append(right, n, weight));
   all {
       adler_byte_sum(left, n) == adler_byte_sum(right, n) => {
           rewrite(adler_byte_sum(left, n), adler_byte_sum(left, n - 1) + to_integer(left[n - 1] as int32));
           rewrite(adler_byte_sum(right, n), adler_byte_sum(right, n - 1) + to_integer(right[n - 1] as int32));
           rewrite(adler_byte_sum(left, n - 1), adler_byte_sum(right, n - 1));
           rewrite(left[n - 1], right[n - 1]);
           close();
       }
       adler_weighted_sum(left, n, weight) == adler_weighted_sum(right, n, weight) => {
           rewrite(adler_weighted_sum(left, n, weight), adler_weighted_sum(left, n - 1, weight) + (to_integer(weight) - to_integer(n - 1)) * to_integer(left[n - 1] as int32));
           rewrite(adler_weighted_sum(right, n, weight), adler_weighted_sum(right, n - 1, weight) + (to_integer(weight) - to_integer(n - 1)) * to_integer(right[n - 1] as int32));
           rewrite(adler_weighted_sum(left, n - 1, weight), adler_weighted_sum(right, n - 1, weight));
           rewrite(left[n - 1], right[n - 1]);
           close();
       }
   }
  }
 }
}

theorem adler_spec_extensional(left: uint8[], right: uint8[], length: int32, a0: Integer, b0: Integer) {
 requires 0 <= length;
 requires forall (k: int32) { 0 <= k and k < length implies left[k] == right[k] };
 ensures adler_spec_a(left, length, a0) == adler_spec_a(right, length, a0) and adler_spec_b(left, length, a0, b0) == adler_spec_b(right, length, a0, b0) by {
  apply(adler_sums_extensional(left, right, length, length, length));
  all {
      adler_spec_a(left, length, a0) == adler_spec_a(right, length, a0) => {
          unfold(adler_spec_a(left, length, a0));
          unfold(adler_spec_a(right, length, a0));
          rewrite(adler_byte_sum(left, length), adler_byte_sum(right, length));
          close();
      }
      adler_spec_b(left, length, a0, b0) == adler_spec_b(right, length, a0, b0) => {
          unfold(adler_spec_b(left, length, a0, b0));
          unfold(adler_spec_b(right, length, a0, b0));
          rewrite(adler_weighted_sum(left, length, length), adler_weighted_sum(right, length, length));
          close();
      }
  }
 }
}
