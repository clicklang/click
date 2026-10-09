# Shared Adler-32 specification over a logical byte snapshot.
# The caller supplies a nonnegative signed-range length and canonical seeds.
# These are mathematical lemmas; neither implementation's result is assumed.

function adler_byte_sum(bytes: uint8[], end: int32) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer((int32)bytes[k]) })
}
function adler_weighted_sum(bytes: uint8[], end: int32, weight_end: int32) -> Integer {
 (0..end).fold(0, |acc, k| {
  acc + (to_integer(weight_end) - to_integer(k)) * to_integer((int32)bytes[k])
 })
}
function adler_spec_a(bytes: uint8[], length: int32, a0: Integer) -> Integer {
 truncating_remainder(a0 + adler_byte_sum(bytes, length), 65521)
}
function adler_spec_b(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 truncating_remainder(b0 + to_integer(length) * a0 + adler_weighted_sum(bytes, length, length), 65521)
}
theorem adler_sum_empty(bytes: uint8[], weight_end: int32) {
 ensures adler_byte_sum(bytes, 0) == 0 by { peel(adler_byte_sum(bytes, 0)) using { 0 >= 0; } simp(); }
 ensures adler_weighted_sum(bytes, 0, weight_end) == 0 by { peel(adler_weighted_sum(bytes, 0, weight_end)) using { 0 >= 0; } simp(); }
}

theorem adler_sum_append(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
  peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 2147483647; }
  normalize();
 }
}
theorem adler_weighted_append(bytes: uint8[], n: int32, weight_end: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, weight_end) == adler_weighted_sum(bytes, n - 1, weight_end) + (to_integer(weight_end) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
  peel(adler_weighted_sum(bytes, n, weight_end)) using { 0 <= n - 1; n - 1 < 2147483647; }
  normalize();
 }
}

theorem adler_weight_shift(bytes: uint8[], n: int32, w0: int32, w1: int32) {
 requires 0 <= n;
 ensures adler_weighted_sum(bytes, n, w1) - adler_weighted_sum(bytes, n, w0) == (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, w1)) using { n <= 0; }
   peel(adler_weighted_sum(bytes, n, w0)) using { n <= 0; }
   peel(adler_byte_sum(bytes, n)) using { n <= 0; }
   have adler_weighted_sum(bytes, n, w1) == 0 by { assumption(); }
   have adler_weighted_sum(bytes, n, w0) == 0 by { assumption(); }
   have adler_byte_sum(bytes, n) == 0 by { assumption(); }
   arithmetic() using { adler_weighted_sum(bytes, n, w1) == 0; adler_weighted_sum(bytes, n, w0) == 0; adler_byte_sum(bytes, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   have n - 1 < 2147483647 by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   peel(adler_weighted_sum(bytes, n, w1)) using { 0 <= n - 1; n - 1 < 2147483647; }
   peel(adler_weighted_sum(bytes, n, w0)) using { 0 <= n - 1; n - 1 < 2147483647; }
   peel(adler_byte_sum(bytes, n)) using { 0 <= n - 1; n - 1 < 2147483647; }
   have (adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]) by {
    arithmetic_certificate special {
     integer_polynomial_identity bounds [] => (adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]);
     conclusion 0;
    }
   }
   rewrite((adler_weighted_sum(bytes, n - 1, w1) + (to_integer(w1) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) - (adler_weighted_sum(bytes, n - 1, w0) + (to_integer(w0) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1])) == (adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0)) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]));
   rewrite(adler_weighted_sum(bytes, n - 1, w1) - adler_weighted_sum(bytes, n - 1, w0) == (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n - 1));
   arithmetic_certificate special {
    integer_polynomial_identity bounds [] => (to_integer(w1) - to_integer(w0)) * adler_byte_sum(bytes, n - 1) + (to_integer(w1) - to_integer(w0)) * to_integer((int32)bytes[n - 1]) == (to_integer(w1) - to_integer(w0)) * (adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
    conclusion 0;
   }
  }
 }
}

theorem adler_weighted_prefix_step(bytes: uint8[], n: int32) {
 requires 0 < n;
 ensures adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n) by {
  have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
  have defined(n - 1) by { simp() using { 0 < n; } }
  apply(int32_subtract_to_integer(n, 1)) using { defined(n - 1); }
  have to_integer(n) - to_integer(n - 1) == 1 by { arithmetic() using { to_integer(n - 1) == to_integer(n) - to_integer(1); } }
  apply(adler_weight_shift(bytes, n - 1, n - 1, n)) using { 0 <= n - 1; }
  have adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1) by {
   rewrite(to_integer(n) - to_integer(n - 1) == 1);
   arithmetic() using { }
  }
  have adler_weighted_sum(bytes, n - 1, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1) by {
   rewrite(adler_byte_sum(bytes, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1));
   arithmetic() using { adler_weighted_sum(bytes, n - 1, n) - adler_weighted_sum(bytes, n - 1, n - 1) == (to_integer(n) - to_integer(n - 1)) * adler_byte_sum(bytes, n - 1); to_integer(n) - to_integer(n - 1) == 1; }
  }
  apply(adler_weighted_append(bytes, n, n)) using { 0 < n; }
  apply(adler_sum_append(bytes, n)) using { 0 < n; }
  rewrite(adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n) + (to_integer(n) - to_integer(n - 1)) * to_integer((int32)bytes[n - 1]));
  rewrite(adler_weighted_sum(bytes, n - 1, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n - 1));
  rewrite(to_integer(n) - to_integer(n - 1) == 1);
  rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
  arithmetic() using { }
 }
}

theorem adler_byte_bounds(value: uint8) {
 ensures 0 <= to_integer((int32)value) by {
  have 0 <= (int32)value by { simp(); }
  apply(int32_less_equal_to_integer(0, (int32)value)) using { 0 <= (int32)value; }
  assumption();
 }
 ensures to_integer((int32)value) <= 255 by {
  have (int32)value <= 255 by { simp(); }
  apply(int32_less_equal_to_integer((int32)value, 255)) using { (int32)value <= 255; }
  assumption();
 }
}


theorem adler_sum_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_byte_sum(bytes, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_byte_sum(bytes, n)) using { n <= 0; }
   arithmetic() using { adler_byte_sum(bytes, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   apply(adler_byte_bounds(bytes[n - 1]));
   apply(adler_sum_append(bytes, n)) using { 0 < n; }
   rewrite(adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer((int32)bytes[n - 1]));
   arithmetic() using { 0 <= adler_byte_sum(bytes, n - 1); 0 <= to_integer((int32)bytes[n - 1]); }
  }
 }
}
theorem adler_weighted_nonnegative(bytes: uint8[], n: int32) {
 requires 0 <= n;
 ensures 0 <= adler_weighted_sum(bytes, n, n) by {
  induct(n) as ih;
  if n <= 0 {
   peel(adler_weighted_sum(bytes, n, n)) using { n <= 0; }
   arithmetic() using { adler_weighted_sum(bytes, n, n) == 0; }
  } else {
   have 0 < n by { simp(); }
   have 0 <= n - 1 by { arithmetic() using { 0 < n; } }
   have n - 1 < n by { arithmetic() using { 0 < n; } }
   apply(ih(n - 1)) using { 0 <= n - 1; n - 1 < n; }
   apply(adler_sum_nonnegative(bytes, n)) using { 0 <= n; }
   apply(adler_weighted_prefix_step(bytes, n)) using { 0 < n; }
   rewrite(adler_weighted_sum(bytes, n, n) == adler_weighted_sum(bytes, n - 1, n - 1) + adler_byte_sum(bytes, n));
   arithmetic() using { 0 <= adler_weighted_sum(bytes, n - 1, n - 1); 0 <= adler_byte_sum(bytes, n); }
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
   have q <= -1 by { arithmetic() using { q < 0; } }
   have n <= -1 by { arithmetic() using { n == q * 65521 + r; q <= -1; r <= 65520; } }
   have not (0 <= n) by { arithmetic() using { n <= -1; } }
   contradiction(0 <= n);
  } else {
   have 0 <= q by { arithmetic() using { not (q < 0); } }
   have q * 65521 <= n by { arithmetic() using { n == q * 65521 + r; 0 <= r; } }
   have n < (q + 1) * 65521 by { arithmetic() using { n == q * 65521 + r; r <= 65520; } }
   have 0 < q + 1 by { arithmetic() using { 0 <= q; } }
   apply(integer_positive_divisor_quotient_lower(n, 65521, q)) using { 65521 != 0; 1 <= 65521; q * 65521 <= n; }
   apply(integer_positive_divisor_quotient_strict_upper(n, 65521, q + 1)) using { 65521 != 0; 1 <= 65521; 0 < q + 1; n < (q + 1) * 65521; }
   have truncating_quotient(n, 65521) == q by { arithmetic() using { q <= truncating_quotient(n, 65521); truncating_quotient(n, 65521) < q + 1; } }
   apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; }
   arithmetic() using { n == q * 65521 + r; n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); truncating_quotient(n, 65521) == q; }
  }
 }
}

theorem adler_residue_add(n: Integer, m: Integer) {
 requires 0 <= n;
 requires 0 <= m;
 ensures truncating_remainder(n + m, 65521) == truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
  apply(integer_truncation_identity(n, 65521)) using { 65521 != 0; }
  apply(integer_truncation_identity(m, 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(n, 65521)) using { 65521 != 0; 0 <= n; }
  apply(integer_nonnegative_dividend_remainder(m, 65521)) using { 65521 != 0; 0 <= m; }
  have 0 <= n + m by { arithmetic() using { 0 <= n; 0 <= m; } }
  have 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521) by { arithmetic() using { 0 <= truncating_remainder(n, 65521); 0 <= truncating_remainder(m, 65521); } }
  apply(integer_truncation_identity(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; }
  apply(integer_nonnegative_dividend_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 <= truncating_remainder(n, 65521) + truncating_remainder(m, 65521); }
  apply(integer_positive_divisor_remainder_upper(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) using { 65521 != 0; 0 < 65521; }
  have n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) by {
   arithmetic() using { n == truncating_quotient(n, 65521) * 65521 + truncating_remainder(n, 65521); m == truncating_quotient(m, 65521) * 65521 + truncating_remainder(m, 65521); truncating_remainder(n, 65521) + truncating_remainder(m, 65521) == truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521); }
  }
  apply(adler_residue_unique(n + m, truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521), truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521))) using {
   0 <= n + m;
   n + m == (truncating_quotient(n, 65521) + truncating_quotient(m, 65521) + truncating_quotient(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521)) * 65521 + truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   0 <= truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521);
   truncating_remainder(truncating_remainder(n, 65521) + truncating_remainder(m, 65521), 65521) <= 65520;
  }
  assumption();
 }
}

function adler_spec_checksum(bytes: uint8[], length: int32, a0: Integer, b0: Integer) -> Integer {
 65536 * adler_spec_b(bytes, length, a0, b0) + adler_spec_a(bytes, length, a0)
}

theorem adler_spec_a_canonical(bytes: uint8[], n: int32, a0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 ensures 0 <= adler_spec_a(bytes, n, a0) and adler_spec_a(bytes, n, a0) <= 65520 by {
  apply(adler_sum_nonnegative(bytes, n)) using { 0 <= n; }
  have 0 <= a0 + adler_byte_sum(bytes, n) by { arithmetic() using { 0 <= a0; 0 <= adler_byte_sum(bytes, n); } }
  apply(integer_nonnegative_dividend_remainder(a0 + adler_byte_sum(bytes, n), 65521)) using { 65521 != 0; 0 <= a0 + adler_byte_sum(bytes, n); }
  apply(integer_positive_divisor_remainder_upper(a0 + adler_byte_sum(bytes, n), 65521)) using { 65521 != 0; 0 < 65521; }
  unfold(adler_spec_a(bytes, n, a0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_b_canonical(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_b(bytes, n, a0, b0) and adler_spec_b(bytes, n, a0, b0) <= 65520 by {
  apply(adler_weighted_nonnegative(bytes, n)) using { 0 <= n; }
  apply(int32_less_equal_to_integer(0, n)) using { 0 <= n; }
  have n <= 2147483647 by { normalize(); }
  apply(int32_less_equal_to_integer(n, 2147483647)) using { n <= 2147483647; }
  have 0 <= to_integer(n) * a0 by {
   arithmetic_certificate special {
    premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
    premise 1: to_integer(n) <= 2147483647 => to_integer(n) <= 2147483647;
    premise 2: 0 <= a0 => 0 <= a0;
    premise 3: a0 <= 65520 => a0 <= 65520;
    integer_product_bounds bounds [0, 1, 2, 3] => 0 <= to_integer(n) * a0;
    conclusion 0;
   }
  }
  have 0 <= b0 + to_integer(n) * a0 by { arithmetic() using { 0 <= b0; 0 <= to_integer(n) * a0; } }
  have 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n) by { arithmetic() using { 0 <= b0 + to_integer(n) * a0; 0 <= adler_weighted_sum(bytes, n, n); } }
  apply(integer_nonnegative_dividend_remainder(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521)) using { 65521 != 0; 0 <= b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n); }
  apply(integer_positive_divisor_remainder_upper(b0 + to_integer(n) * a0 + adler_weighted_sum(bytes, n, n), 65521)) using { 65521 != 0; 0 < 65521; }
  unfold(adler_spec_b(bytes, n, a0, b0));
  both { assumption(); } and { assumption(); }
 }
}

theorem adler_spec_packing_bounds(bytes: uint8[], n: int32, a0: Integer, b0: Integer) {
 requires 0 <= n;
 requires 0 <= a0;
 requires a0 <= 65520;
 requires 0 <= b0;
 ensures 0 <= adler_spec_checksum(bytes, n, a0, b0) and adler_spec_checksum(bytes, n, a0, b0) <= 4293984240 by {
  apply(adler_spec_a_canonical(bytes, n, a0)) using { 0 <= n; 0 <= a0; }
  apply(adler_spec_b_canonical(bytes, n, a0, b0)) using { 0 <= n; 0 <= a0; a0 <= 65520; 0 <= b0; }
  unfold(adler_spec_checksum(bytes, n, a0, b0));
  both {
   arithmetic() using { 0 <= adler_spec_b(bytes, n, a0, b0); 0 <= adler_spec_a(bytes, n, a0); }
  } and {
   arithmetic() using { adler_spec_b(bytes, n, a0, b0) <= 65520; adler_spec_a(bytes, n, a0) <= 65520; }
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
  have a0 == 0 * 65521 + a0 by { arithmetic() using {}; }
  apply(adler_residue_unique(a0, 0, a0)) using { 0 <= a0; a0 == 0 * 65521 + a0; 0 <= a0; a0 <= 65520; }
  unfold(adler_spec_a(bytes, 0, a0));
  rewrite(adler_byte_sum(bytes, 0) == 0);
  simp() using { truncating_remainder(a0, 65521) == a0; }
 }
 ensures adler_spec_b(bytes, 0, a0, b0) == b0 by {
  apply(adler_sum_empty(bytes, 0));
  have b0 == 0 * 65521 + b0 by { arithmetic() using {}; }
  apply(adler_residue_unique(b0, 0, b0)) using { 0 <= b0; b0 == 0 * 65521 + b0; 0 <= b0; b0 <= 65520; }
  unfold(adler_spec_b(bytes, 0, a0, b0));
  rewrite(adler_weighted_sum(bytes, 0, 0) == 0);
  simp() using { truncating_remainder(b0, 65521) == b0; }
 }
}
