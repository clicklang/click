import click::integer;
import "adler32-spec.click";
import "adler32-spec-u64.click";

// The int32 and uint64 Adler-32 specifications agree at every length both
// can state: an int32 length and a uint64 length with one exact value give
// the same sums and the same checksum, byte for byte.

theorem adler_byte_widen(value: uint8) {
 ensures to_integer(value as int32) == to_integer(value) by {
  have 0 <= value as int32 by solve();
  have value as int32 <= 255 by solve();
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as int32) == to_integer(value);
   conclusion 0;
  }
 }
}

theorem adler_byte_sum_bridge(bytes: uint8[], m: uint64) {
 ensures forall (n: int32) { to_integer(n) == to_integer(m) implies adler_byte_sum(bytes, n) == adler_byte_sum_u64(bytes, m) } by {
  induct(m) as ih;
  intro();
  intro();
  if m <= 0u64 {
   have m == 0u64 by solve() using { m <= 0u64; };
   have n == 0 by solve() using { to_integer(n) == to_integer(m); m == 0u64; };
   rewrite(m == 0u64);
   rewrite(n == 0);
   apply(adler_sum_empty(bytes, 0));
   apply(adler_sum_empty_u64(bytes, 0));
   solve();
  } else {
   have 0u64 < m by solve();
   have 0 < n by solve() using { to_integer(n) == to_integer(m); 0u64 < m; };
   have to_integer(m - 1u64) < to_integer(m) by solve() using { 0u64 < m; };
   have defined(n - 1) by solve() using { 0 < n; };
   have to_integer(n - 1) == to_integer(n) - to_integer(1);
   have 1u64 <= m by solve() using { 0u64 < m; };
   have to_integer(m - 1u64) == to_integer(m) - to_integer(1u64);
   have to_integer(n - 1) == to_integer(m - 1u64) by solve() using { to_integer(n) == to_integer(m); to_integer(n - 1) == to_integer(n) - to_integer(1); to_integer(m - 1u64) == to_integer(m) - to_integer(1u64); };
   apply(ih(m - 1u64)) using { to_integer(m - 1u64) < to_integer(m); };
   instantiate(forall (n: int32) { to_integer(n) == to_integer(m - 1u64) implies adler_byte_sum(bytes, n) == adler_byte_sum_u64(bytes, m - 1u64) }, n - 1);
   apply(adler_sum_append(bytes, n)) using { 0 < n; };
   apply(adler_sum_append_u64(bytes, m)) using { 0u64 < m; };
   have bytes + (n - 1) == bytes + (m - 1u64) by normalize() using { to_integer(n - 1) == to_integer(m - 1u64); };
   have to_integer(bytes[n - 1] as int32) == to_integer(bytes[m - 1u64]) by {
    rewrite(bytes + (n - 1) == bytes + (m - 1u64));
    apply(adler_byte_widen(bytes[m - 1u64]));
   }
   solve() using {
    adler_byte_sum(bytes, n) == adler_byte_sum(bytes, n - 1) + to_integer(bytes[n - 1] as int32);
    adler_byte_sum_u64(bytes, m) == adler_byte_sum_u64(bytes, m - 1u64) + to_integer(bytes[m - 1u64]);
    adler_byte_sum(bytes, n - 1) == adler_byte_sum_u64(bytes, m - 1u64);
    to_integer(bytes[n - 1] as int32) == to_integer(bytes[m - 1u64]);
   };
  }
 }
}

theorem adler_weighted_sum_bridge(bytes: uint8[], m: uint64, w: int32) {
 ensures forall (n: int32) { to_integer(n) == to_integer(m) implies adler_weighted_sum(bytes, n, w) == adler_weighted_sum_u64(bytes, m, to_integer(w)) } by {
  induct(m) as ih;
  intro();
  intro();
  if m <= 0u64 {
   have m == 0u64 by solve() using { m <= 0u64; };
   have n == 0 by solve() using { to_integer(n) == to_integer(m); m == 0u64; };
   rewrite(m == 0u64);
   rewrite(n == 0);
   apply(adler_sum_empty(bytes, w));
   apply(adler_sum_empty_u64(bytes, to_integer(w)));
   solve();
  } else {
   have 0u64 < m by solve();
   have 0 < n by solve() using { to_integer(n) == to_integer(m); 0u64 < m; };
   have to_integer(m - 1u64) < to_integer(m) by solve() using { 0u64 < m; };
   have defined(n - 1) by solve() using { 0 < n; };
   have to_integer(n - 1) == to_integer(n) - to_integer(1);
   have 1u64 <= m by solve() using { 0u64 < m; };
   have to_integer(m - 1u64) == to_integer(m) - to_integer(1u64);
   have to_integer(n - 1) == to_integer(m - 1u64) by solve() using { to_integer(n) == to_integer(m); to_integer(n - 1) == to_integer(n) - to_integer(1); to_integer(m - 1u64) == to_integer(m) - to_integer(1u64); };
   apply(ih(m - 1u64)) using { to_integer(m - 1u64) < to_integer(m); };
   instantiate(forall (n: int32) { to_integer(n) == to_integer(m - 1u64) implies adler_weighted_sum(bytes, n, w) == adler_weighted_sum_u64(bytes, m - 1u64, to_integer(w)) }, n - 1);
   apply(adler_weighted_append(bytes, n, w)) using { 0 < n; };
   apply(adler_weighted_append_u64(bytes, m, to_integer(w))) using { 0u64 < m; };
   have bytes + (n - 1) == bytes + (m - 1u64) by normalize() using { to_integer(n - 1) == to_integer(m - 1u64); };
   have to_integer(bytes[n - 1] as int32) == to_integer(bytes[m - 1u64]) by {
    rewrite(bytes + (n - 1) == bytes + (m - 1u64));
    apply(adler_byte_widen(bytes[m - 1u64]));
   }
   rewrite(adler_weighted_sum(bytes, n, w) == adler_weighted_sum(bytes, n - 1, w) + (to_integer(w) - to_integer(n - 1)) * to_integer(bytes[n - 1] as int32));
   rewrite(adler_weighted_sum_u64(bytes, m, to_integer(w)) == adler_weighted_sum_u64(bytes, m - 1u64, to_integer(w)) + (to_integer(w) - to_integer(m - 1u64)) * to_integer(bytes[m - 1u64]));
   rewrite(adler_weighted_sum(bytes, n - 1, w) == adler_weighted_sum_u64(bytes, m - 1u64, to_integer(w)));
   rewrite(to_integer(n - 1) == to_integer(m - 1u64));
   rewrite(to_integer(bytes[n - 1] as int32) == to_integer(bytes[m - 1u64]));
   normalize();
  }
 }
}

theorem adler_spec_a_bridge(bytes: uint8[], n: int32, m: uint64, a0: Integer) {
 requires to_integer(n) == to_integer(m);
 ensures adler_spec_a(bytes, n, a0) == adler_spec_a_u64(bytes, m, a0) by {
  apply(adler_byte_sum_bridge(bytes, m));
  instantiate(forall (n: int32) { to_integer(n) == to_integer(m) implies adler_byte_sum(bytes, n) == adler_byte_sum_u64(bytes, m) }, n);
  unfold(adler_spec_a(bytes, n, a0));
  unfold(adler_spec_a_u64(bytes, m, a0));
  rewrite(adler_byte_sum(bytes, n) == adler_byte_sum_u64(bytes, m));
  normalize();
 }
}

theorem adler_spec_b_bridge(bytes: uint8[], n: int32, m: uint64, a0: Integer, b0: Integer) {
 requires to_integer(n) == to_integer(m);
 ensures adler_spec_b(bytes, n, a0, b0) == adler_spec_b_u64(bytes, m, a0, b0) by {
  apply(adler_weighted_sum_bridge(bytes, m, n));
  instantiate(forall (k: int32) { to_integer(k) == to_integer(m) implies adler_weighted_sum(bytes, k, n) == adler_weighted_sum_u64(bytes, m, to_integer(n)) }, n);
  unfold(adler_spec_b(bytes, n, a0, b0));
  unfold(adler_spec_b_u64(bytes, m, a0, b0));
  rewrite(adler_weighted_sum(bytes, n, n) == adler_weighted_sum_u64(bytes, m, to_integer(n)));
  rewrite(to_integer(n) == to_integer(m));
  normalize();
 }
}

theorem adler_spec_checksum_bridge(bytes: uint8[], n: int32, m: uint64, a0: Integer, b0: Integer) {
 requires to_integer(n) == to_integer(m);
 ensures adler_spec_checksum(bytes, n, a0, b0) == adler_spec_checksum_u64(bytes, m, a0, b0) by {
  apply(adler_spec_a_bridge(bytes, n, m, a0)) using { to_integer(n) == to_integer(m); };
  apply(adler_spec_b_bridge(bytes, n, m, a0, b0)) using { to_integer(n) == to_integer(m); };
  unfold(adler_spec_checksum(bytes, n, a0, b0));
  unfold(adler_spec_checksum_u64(bytes, m, a0, b0));
  rewrite(adler_spec_a(bytes, n, a0) == adler_spec_a_u64(bytes, m, a0));
  rewrite(adler_spec_b(bytes, n, a0, b0) == adler_spec_b_u64(bytes, m, a0, b0));
  normalize();
 }
}
