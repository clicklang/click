import "batch-helpers.click";

// Native DO16 arithmetic for a batch entered with reduced components.
theorem zlib_seeded_component_step(bytes: uint8[], n: int32, a: uint64, b: uint64, value: uint8, a0: uint64, b0: uint64) {
 requires a0 <= 65520u64;
 requires b0 <= 65520u64;
 requires 0 <= n;
 requires n < 5552;
 requires (int32)value == (int32)bytes[n];
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
 requires to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
 requires to_integer(a) <= 65520 + 255 * to_integer(n);
 requires to_integer(b) <= 65520 + 1481280 * to_integer(n);
 ensures to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1)
     and to_integer(a + (uint64)(uint32)value) <= 65520 + 255 * to_integer(n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) <= 65520 + 1481280 * to_integer(n + 1) by {
  have n <= 5551 by arithmetic() using { n < 5552; };
  have n < 2147483647 by arithmetic() using { n < 5552; };
  apply(int32_less_equal_to_integer(n, 5551));
  have defined(n + 1) by simp();
  apply(int32_add_to_integer(n, 1));
  apply(zlib_byte_u64(value));
  apply(zlib_byte_integer_identity(value));
  apply(zlib_equal_byte_integers(value, bytes[n]));
  apply(zlib_component_step(bytes, n));
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280 by arithmetic() using {
   to_integer(a) <= 65520 + 255 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
  };
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using { to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280; };
  apply(uint64_add_to_integer(a, (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) <= 1481280 by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) + to_integer((uint64)(uint32)value) <= 1481280;
  };
  have to_integer(b) + to_integer(a + (uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using {
   to_integer(b) <= 65520 + 1481280 * to_integer(n);
   to_integer(n) <= 5551;
   to_integer(a + (uint64)(uint32)value) <= 1481280;
  };
  apply(uint64_add_to_integer(b, a + (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   zlib_byte_integer(value) == to_integer((int32)value);
   zlib_byte_integer(value) == zlib_byte_integer(bytes[n]);
   adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + zlib_byte_integer(bytes[n]);
  };
  have to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0) by {
   rewrite(to_integer(n + 1) == to_integer(n) + to_integer(1));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (to_integer(n) + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0); conclusion 0;
   }
  }
  have to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
   to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1);
   adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1);
   to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0);
  };
  have to_integer(a + (uint64)(uint32)value) <= 65520 + 255 * to_integer(n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) <= 65520 + 255 * to_integer(n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  have to_integer(b + (a + (uint64)(uint32)value)) <= 65520 + 1481280 * to_integer(n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) <= 65520 + 1481280 * to_integer(n);
   to_integer(a + (uint64)(uint32)value) <= 1481280;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  simp();
 }
}

// The original MOD operations return canonical components for this local batch.
theorem zlib_seeded_reduced_components(bytes: uint8[], length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, length, to_integer(a0)) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  unfold(adler_spec_a(bytes, length, to_integer(a0)));
  rewrite(to_integer(a0) + adler_byte_sum(bytes, length) == to_integer(a)); assumption();
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, length, to_integer(a0), to_integer(b0)) by {
  apply(uint64_remainder_to_integer(b, 65521u64));
  unfold(adler_spec_b(bytes, length, to_integer(a0), to_integer(b0)));
  rewrite(to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes, length, length) == to_integer(b)); assumption();
 }
 ensures a % 65521u64 <= 65520u64 and b % 65521u64 <= 65520u64 by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65520 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= 65521 - 1;
  };
  have to_integer(b % 65521u64) <= 65520 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(a % 65521u64, 65520u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65520u64)); simp();
 }
}

// Connect the next batch's native seeds to the previously processed prefix.
// No C computation is assumed: the raw component equations are premises.
theorem zlib_seeded_batch_concat(bytes: uint8[], prefix: int32, length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires 0 <= prefix;
 requires 0 <= length;
 requires prefix <= 2147483647 - length;
 requires defined(prefix + length);
 requires to_integer(a0) == adler_spec_a(bytes, prefix, 1);
 requires to_integer(b0) == adler_spec_b(bytes, prefix, 1, 0);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, 1) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_a_concat(bytes, prefix, length, 1));
  have to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0)); assumption();
  }
  arithmetic() using {
   to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1));
   adler_spec_a(bytes, prefix + length, 1) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1));
  };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, 1, 0) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_b_concat(bytes, prefix, length, 1, 0));
  have to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0));
   rewrite(adler_spec_b(bytes, prefix, 1, 0) == to_integer(b0)); assumption();
  }
  arithmetic() using {
   to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0));
   adler_spec_b(bytes, prefix + length, 1, 0) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0));
  };
 }
}

// Bound a native cursor within a full caller view after the NMAX subtraction.
theorem zlib_stream_batch_read_bound(total: uint64, remaining: uint64, n: uint32) {
 requires 5552u64 <= total;
 requires total <= 22208u64;
 requires remaining <= total - 5552u64;
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; }
 ensures 5552u64 <= total - remaining by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; }
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= total - 16u64 by {
  apply(zlib_batch_nonempty_remaining(n));
  apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  arithmetic() using {
   remaining <= total; 5552u64 <= total - remaining;
   5552u64 <= total; total <= 22208u64;
   16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64;
  };
 }
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) < total by {
  apply(zlib_batch_nonempty_remaining(n)); apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  arithmetic() using { remaining <= total; 5552u64 <= total - remaining; 5552u64 <= total; total <= 22208u64; 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; }
 }
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + 16u64 <= total by {
  apply(zlib_batch_nonempty_remaining(n)); apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 22208u64; };
  arithmetic() using { remaining <= total; 5552u64 <= total - remaining; 5552u64 <= total; total <= 22208u64; 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; }
 }

}

theorem zlib_native_cursor_join(base: const uint8*, first: uint64, second: uint64) {
 requires first <= 22208u64;
 requires second <= 5552u64;
 requires first + second <= 22208u64;
 ensures base + first + second == base + (first + second) by {
  apply(uint64_less_equal_to_integer(first, 22208u64));
  apply(uint64_less_equal_to_integer(second, 5552u64));
  have to_integer(first) + to_integer(second) <= 18446744073709551615 by arithmetic() using {
   to_integer(first) <= to_integer(22208u64); to_integer(second) <= to_integer(5552u64);
  };
  apply(uint64_add_to_integer(first, second));
  have second <= 22208u64 by arithmetic() using { second <= 5552u64; };
  apply(adler_count_observation(first)); apply(adler_count_bounds(first));
  apply(adler_count_observation(second)); apply(adler_count_bounds(second));
  apply(adler_count_observation(first + second));
  have defined((int32)(uint32)first + (int32)(uint32)second) by simp();
  apply(int32_add_to_integer((int32)(uint32)first, (int32)(uint32)second));
  have to_integer((int32)(uint32)(first + second)) == to_integer((int32)(uint32)first + (int32)(uint32)second) by arithmetic() using {
   to_integer((int32)(uint32)(first + second)) == to_integer(first + second);
   to_integer(first + second) == to_integer(first) + to_integer(second);
   to_integer((int32)(uint32)first) == to_integer(first);
   to_integer((int32)(uint32)second) == to_integer(second);
   to_integer((int32)(uint32)first + (int32)(uint32)second) == to_integer((int32)(uint32)first) + to_integer((int32)(uint32)second);
  };
  apply(int32_to_integer_equal_implies_equal((int32)(uint32)(first + second), (int32)(uint32)first + (int32)(uint32)second));
  apply(adler_count_byte_pointer(base, first));
  apply(adler_count_byte_pointer(base + first, second));
  apply(adler_count_byte_pointer(base, first + second));
  rewrite(base + first + second == base + first + (int32)(uint32)second);
  rewrite(base + first == base + (int32)(uint32)first);
  rewrite(base + (first + second) == base + (int32)(uint32)(first + second));
  rewrite((int32)(uint32)(first + second) == (int32)(uint32)first + (int32)(uint32)second);
  normalize() using { defined((int32)(uint32)first + (int32)(uint32)second); }
 }
}

theorem zlib_stream_batch_lane_bound(total: uint64, remaining: uint64, n: uint32, lane: uint64) {
 requires 5552u64 <= total;
 requires total <= 22208u64;
 requires remaining <= total - 5552u64;
 requires 1u32 <= n;
 requires n <= 347u32;
 requires lane <= 15u64;
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane < total by {
  apply(zlib_stream_batch_read_bound(total, remaining, n));
  apply(zlib_batch_remaining_limit(n));
  have (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= 22208u64 by arithmetic() using {
   (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= total - 16u64;
   remaining <= total; 5552u64 <= total - remaining;
   5552u64 <= total; total <= 22208u64; zlib_batch_remaining(n) <= 5552u64;
  };
  apply(uint64_less_equal_to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)), 22208u64));
  apply(uint64_less_equal_to_integer(lane, 15u64));
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane) <= 18446744073709551615 by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(22208u64); to_integer(lane) <= to_integer(15u64);
  };
  apply(uint64_add_to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)), lane));
  apply(uint64_less_equal_to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)), total - 16u64));
  apply(uint64_less_equal_to_integer(5552u64, total));
  have to_integer(16u64) <= to_integer(total) by arithmetic() using { to_integer(5552u64) <= to_integer(total); };
  apply(uint64_subtract_to_integer(total, 16u64));
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane) < to_integer(total) by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane) == to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane);
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(total - 16u64);
   to_integer(total - 16u64) == to_integer(total) - to_integer(16u64);
   to_integer(lane) <= to_integer(15u64);
  };
  apply(uint64_to_integer_less_than_implies_less_than((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane, total)); assumption();
 }
}

theorem zlib_stream_remaining_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 22208u64;
 requires amount <= remaining;
 ensures remaining - amount <= total by arithmetic() using { remaining <= total; total <= 22208u64; amount <= remaining; }
 ensures total - (remaining - amount) <= 22208u64 by arithmetic() using { remaining <= total; total <= 22208u64; amount <= remaining; }
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  apply(uint64_less_equal_to_integer(amount, remaining));
  apply(uint64_subtract_to_integer(remaining, amount)); assumption();
 }
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount) by {
  have total - remaining <= 22208u64 by arithmetic() using { remaining <= total; total <= 22208u64; };
  have remaining - amount <= total by arithmetic() using { remaining <= total; total <= 22208u64; amount <= remaining; };
  have total - (remaining - amount) <= 22208u64 by arithmetic() using { remaining <= total; total <= 22208u64; amount <= remaining; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_observation(total, remaining - amount));
  apply(uint64_less_equal_to_integer(remaining, total));
  apply(uint64_less_equal_to_integer(amount, remaining));
  apply(uint64_less_equal_to_integer(remaining - amount, total));
  apply(uint64_subtract_to_integer(total, remaining));
  apply(uint64_subtract_to_integer(total, remaining - amount));
  apply(uint64_subtract_to_integer(remaining, amount));
  arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount));
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount);
  };
 }
}


theorem zlib_stream_prefix_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 22208u64;
 requires amount <= remaining;
 ensures zlib_prefix_count(total, remaining - amount) == zlib_prefix_count(total, remaining) + (int32)(uint32)amount by {
  apply(zlib_stream_remaining_step(total, remaining, amount));
  have total - remaining <= 22208u64 by arithmetic() using { remaining <= total; total <= 22208u64; };
  have amount <= 22208u64 by arithmetic() using { amount <= remaining; remaining <= total; total <= 22208u64; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_observation(total, remaining - amount));
  apply(adler_count_observation(amount)); apply(adler_count_bounds(amount));
  have defined(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by simp();
  apply(int32_add_to_integer(zlib_prefix_count(total, remaining), (int32)(uint32)amount));
  have to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount);
   to_integer((int32)(uint32)amount) == to_integer(amount);
   to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) == to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount);
  };
  apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(total, remaining - amount), zlib_prefix_count(total, remaining) + (int32)(uint32)amount)); assumption();
 }
}

theorem zlib_stream_capacity_step(n: uint32, remaining: uint64) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires remaining <= 16656u64;
 ensures 16u64 * (uint64)n + remaining <= 22208u64
     and 16u64 * (uint64)(n - 1u32) + remaining == 16u64 * (uint64)n + remaining - 16u64
     and 16u64 * (uint64)(n - 1u32) + remaining <= 22208u64 by {
  apply(uint32_less_equal_to_integer(1u32, n)); apply(uint32_less_equal_to_integer(n, 347u32));
  apply(uint32_subtract_to_integer(n, 1u32)); apply(zlib_batch_predecessor(n));
  apply(uint32_less_equal_to_integer(n - 1u32, 347u32));
  apply(zlib_batch_native_capacity_observation(n)); apply(zlib_batch_native_capacity_observation(n - 1u32));
  apply(uint64_less_equal_to_integer(remaining, 16656u64)); apply(uint64_to_integer_bounds(remaining));
  have to_integer(16u64 * (uint64)n) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); to_integer(n) <= 347; };
  have to_integer(16u64 * (uint64)(n - 1u32)) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32); to_integer(n - 1u32) <= 347; };
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n) by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); 1 <= to_integer(n); };
  have to_integer(16u64 * (uint64)n) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 16656; };
  have to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 16656; };
  apply(uint64_add_to_integer(16u64 * (uint64)n, remaining)); apply(uint64_add_to_integer(16u64 * (uint64)(n - 1u32), remaining));
  have to_integer(16u64 * (uint64)n + remaining) <= to_integer(22208u64) by arithmetic() using {
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
   to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 16656;
  };
  have to_integer(16u64 * (uint64)(n - 1u32) + remaining) <= to_integer(22208u64) by arithmetic() using {
   to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining);
   to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 16656;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(16u64 * (uint64)n + remaining, 22208u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(16u64 * (uint64)(n - 1u32) + remaining, 22208u64));
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n + remaining) by arithmetic() using {
   to_integer(16u64) <= to_integer(16u64 * (uint64)n); 0 <= to_integer(remaining);
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
  };
  apply(uint64_subtract_to_integer(16u64 * (uint64)n + remaining, 16u64));
  have to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)n + remaining - 16u64) by arithmetic() using {
   to_integer(16u64 * (uint64)n) == 16 * to_integer(n);
   to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32);
   to_integer(n - 1u32) == to_integer(n) - to_integer(1u32);
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
   to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining);
   to_integer(16u64 * (uint64)n + remaining - 16u64) == to_integer(16u64 * (uint64)n + remaining) - to_integer(16u64);
  };
  apply(uint64_to_integer_equal_implies_equal(16u64 * (uint64)(n - 1u32) + remaining, 16u64 * (uint64)n + remaining - 16u64)); simp();
 }
}

theorem zlib_stream_tail_read_bound(total: uint64, remaining: uint64, lane: uint64) {
 requires remaining <= total;
 requires total <= 22208u64;
 requires 16u64 <= remaining;
 requires lane <= 15u64;
 ensures total - remaining <= 22192u64 by arithmetic() using { remaining <= total; total <= 22208u64; 16u64 <= remaining; }
 ensures total - remaining + lane < total by arithmetic() using { remaining <= total; total <= 22208u64; 16u64 <= remaining; lane <= 15u64; }
}

theorem zlib_scalar_seeded_component_step(bytes: uint8[], n: int32, a: uint64, b: uint64, value: uint8, a0: uint64, b0: uint64) {
 requires a0 <= 1500000u64;
 requires b0 <= 10000000000u64;
 requires 0 <= n;
 requires n < 16;
 requires (int32)value == (int32)bytes[n];
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
 requires to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
 requires to_integer(a) <= 1500000 + 255 * to_integer(n);
 requires to_integer(b) <= 10000000000 + 1504080 * to_integer(n);
 ensures to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1)
     and to_integer(a + (uint64)(uint32)value) <= 1500000 + 255 * to_integer(n + 1)
     and to_integer(b + (a + (uint64)(uint32)value)) <= 10000000000 + 1504080 * to_integer(n + 1) by {
  have n <= 15 by arithmetic() using { n < 16; };
  have n < 2147483647 by arithmetic() using { n < 16; };
  apply(int32_less_equal_to_integer(n, 15));
  have defined(n + 1) by simp();
  apply(int32_add_to_integer(n, 1));
  apply(zlib_byte_u64(value));
  apply(zlib_byte_integer_identity(value));
  apply(zlib_equal_byte_integers(value, bytes[n]));
  apply(zlib_component_step(bytes, n));
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 1504080 by arithmetic() using {
   to_integer(a) <= 1500000 + 255 * to_integer(n);
   to_integer(n) <= 15;
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
  };
  have to_integer(a) + to_integer((uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using { to_integer(a) + to_integer((uint64)(uint32)value) <= 1504080; };
  apply(uint64_add_to_integer(a, (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) <= 1504080 by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) + to_integer((uint64)(uint32)value) <= 1504080;
  };
  have to_integer(b) + to_integer(a + (uint64)(uint32)value) <= 18446744073709551615 by arithmetic() using {
   to_integer(b) <= 10000000000 + 1504080 * to_integer(n);
   to_integer(n) <= 15;
   to_integer(a + (uint64)(uint32)value) <= 1504080;
  };
  apply(uint64_add_to_integer(b, a + (uint64)(uint32)value));
  have to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) == to_integer(a0) + adler_byte_sum(bytes, n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   zlib_byte_integer(value) == to_integer((int32)value);
   zlib_byte_integer(value) == zlib_byte_integer(bytes[n]);
   adler_byte_sum(bytes, n + 1) == adler_byte_sum(bytes, n) + zlib_byte_integer(bytes[n]);
  };
  have to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0) by {
   rewrite(to_integer(n + 1) == to_integer(n) + to_integer(1));
   arithmetic_certificate rules {
    integer_polynomial_identity bounds [] => (to_integer(n) + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0); conclusion 0;
   }
  }
  have to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0) + adler_weighted_sum(bytes, n + 1, n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) == to_integer(b0) + to_integer(n) * to_integer(a0) + adler_weighted_sum(bytes, n, n);
   to_integer(a + (uint64)(uint32)value) == to_integer(a0) + adler_byte_sum(bytes, n + 1);
   adler_weighted_sum(bytes, n + 1, n + 1) == adler_weighted_sum(bytes, n, n) + adler_byte_sum(bytes, n + 1);
   to_integer(n + 1) * to_integer(a0) == to_integer(n) * to_integer(a0) + to_integer(a0);
  };
  have to_integer(a + (uint64)(uint32)value) <= 1500000 + 255 * to_integer(n + 1) by arithmetic() using {
   to_integer(a + (uint64)(uint32)value) == to_integer(a) + to_integer((uint64)(uint32)value);
   to_integer(a) <= 1500000 + 255 * to_integer(n);
   to_integer((uint64)(uint32)value) == to_integer((int32)value);
   to_integer((int32)value) <= 255;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  have to_integer(b + (a + (uint64)(uint32)value)) <= 10000000000 + 1504080 * to_integer(n + 1) by arithmetic() using {
   to_integer(b + (a + (uint64)(uint32)value)) == to_integer(b) + to_integer(a + (uint64)(uint32)value);
   to_integer(b) <= 10000000000 + 1504080 * to_integer(n);
   to_integer(a + (uint64)(uint32)value) <= 1504080;
   to_integer(n + 1) == to_integer(n) + to_integer(1);
  };
  simp();
 }
}

theorem zlib_stream_split_count(total: uint64, middle: uint64, remaining: uint64) {
 requires remaining <= middle;
 requires middle <= total;
 requires total <= 22208u64;
 ensures zlib_prefix_count(total, remaining) == zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining) by {
  have remaining <= total by arithmetic() using { remaining <= middle; middle <= total; total <= 22208u64; };
  have middle <= 22208u64 by arithmetic() using { middle <= total; total <= 22208u64; };
  have total - middle <= 22208u64 by arithmetic() using { middle <= total; total <= 22208u64; };
  have total - remaining <= 22208u64 by arithmetic() using { remaining <= total; total <= 22208u64; };
  have middle - remaining <= 22208u64 by arithmetic() using { remaining <= middle; middle <= 22208u64; };
  apply(zlib_prefix_observation(total, middle)); apply(zlib_prefix_observation(total, remaining)); apply(zlib_prefix_observation(middle, remaining));
  apply(uint64_less_equal_to_integer(middle, total)); apply(uint64_less_equal_to_integer(remaining, middle)); apply(uint64_less_equal_to_integer(remaining, total));
  apply(uint64_subtract_to_integer(total, middle)); apply(uint64_subtract_to_integer(total, remaining)); apply(uint64_subtract_to_integer(middle, remaining));
  have defined(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by simp();
  apply(int32_add_to_integer(zlib_prefix_count(total, middle), zlib_prefix_count(middle, remaining)));
  have to_integer(zlib_prefix_count(total, remaining)) == to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) == to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining));
  };
  apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(total, remaining), zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining))); assumption();
 }
}

theorem zlib_raw_seeded_batch_concat(bytes: uint8[], prefix: int32, length: int32, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires 0 <= prefix;
 requires 0 <= length;
 requires prefix <= 2147483647 - length;
 requires defined(prefix + length);
 requires a0 <= 1500000u64;
 requires to_integer(a0 % 65521u64) == adler_spec_a(bytes, prefix, 1);
 requires to_integer(b0 % 65521u64) == adler_spec_b(bytes, prefix, 1, 0);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, 1) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_to_integer_bounds(a0)); apply(uint64_remainder_to_integer(a0, 65521u64));
  apply(adler_sum_nonnegative(bytes + prefix, length));
  apply(adler_residue_add_left(to_integer(a0), adler_byte_sum(bytes + prefix, length)));
  have adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)) by {
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0)));
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)));
   rewrite(to_integer(a0 % 65521u64) == truncating_remainder(to_integer(a0), 65521)); assumption();
  }
  have to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0 % 65521u64));
   arithmetic() using {
    to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, to_integer(a0));
    adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64));
   };
  }
  apply(adler_spec_a_concat(bytes, prefix, length, 1));
  arithmetic() using { to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1)); adler_spec_a(bytes, prefix + length, 1) == adler_spec_a(bytes + prefix, length, adler_spec_a(bytes, prefix, 1)); }
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, 1, 0) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_to_integer_bounds(a0)); apply(uint64_to_integer_bounds(b0));
  apply(uint64_less_equal_to_integer(a0, 1500000u64));
  apply(uint64_remainder_to_integer(a0, 65521u64)); apply(uint64_remainder_to_integer(b0, 65521u64));
  apply(adler_weighted_nonnegative(bytes + prefix, length));
  apply(int32_less_equal_to_integer(0, length));
  have length <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(length, 2147483647));
  have to_integer(a0) <= 549755879424 by arithmetic() using { to_integer(a0) <= 1500000; };
  have 0 <= to_integer(length) by simp() using { to_integer(0) <= to_integer(length); };
  have to_integer(length) <= 2147483647 by simp() using { to_integer(length) <= to_integer(2147483647); };
  apply(adler_residue_seed_update(to_integer(a0), to_integer(b0), to_integer(length), adler_weighted_sum(bytes + prefix, length, length)));
  have adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)) by {
   unfold(adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)));
   unfold(adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)));
   rewrite(to_integer(a0 % 65521u64) == truncating_remainder(to_integer(a0), 65521));
   rewrite(to_integer(b0 % 65521u64) == truncating_remainder(to_integer(b0), 65521)); assumption();
  }
  have to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0)) by {
   rewrite(adler_spec_a(bytes, prefix, 1) == to_integer(a0 % 65521u64));
   rewrite(adler_spec_b(bytes, prefix, 1, 0) == to_integer(b0 % 65521u64));
   arithmetic() using {
    to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0));
    adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64));
   };
  }
  apply(adler_spec_b_concat(bytes, prefix, length, 1, 0));
  arithmetic() using { to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0)); adler_spec_b(bytes, prefix + length, 1, 0) == adler_spec_b(bytes + prefix, length, adler_spec_a(bytes, prefix, 1), adler_spec_b(bytes, prefix, 1, 0)); }
 }
}

theorem zlib_components_pack(bytes: uint8[], length: int32, a: uint64, b: uint64) {
 requires to_integer(a % 65521u64) == adler_spec_a(bytes, length, 1);
 requires to_integer(b % 65521u64) == adler_spec_b(bytes, length, 1, 0);
 ensures to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == adler_spec_checksum(bytes, length, 1, 0) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65535 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= 65521 - 1;
  };
  have to_integer(b % 65521u64) <= 65535 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= 65521 - 1;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(a % 65521u64, 65535u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(b % 65521u64, 65535u64));
  apply(uint64_pack_uint16_to_integer(a % 65521u64, b % 65521u64));
  unfold(adler_spec_checksum(bytes, length, 1, 0));
  arithmetic() using {
   to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == to_integer(a % 65521u64) + 65536 * to_integer(b % 65521u64);
   to_integer(a % 65521u64) == adler_spec_a(bytes, length, 1);
   to_integer(b % 65521u64) == adler_spec_b(bytes, length, 1, 0);
  };
 }
}


theorem zlib_stream_scalar_read_bound(total: uint64, remaining: uint64) {
 requires 1u64 <= remaining; requires remaining <= total; requires total <= 22208u64;
 ensures total - remaining < total by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 22208u64; }
 ensures total - remaining <= 22207u64 by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 22208u64; }
}

theorem zlib_stream_concat_bound(prefix: int32, count: int32) {
 requires 0 <= prefix; requires prefix <= 22208;
 requires 0 <= count; requires count <= 22208;
 ensures prefix <= 2147483647 - count by {
  apply(int32_less_equal_to_integer(prefix, 22208)); apply(int32_less_equal_to_integer(count, 22208)); apply(int32_less_equal_to_integer(0, count));
  have defined(2147483647 - count) by simp();
  apply(int32_subtract_to_integer(2147483647, count));
  have to_integer(prefix) <= to_integer(2147483647 - count) by arithmetic() using { to_integer(prefix) <= 22208; to_integer(count) <= 22208; to_integer(2147483647 - count) == to_integer(2147483647) - to_integer(count); };
  apply(int32_to_integer_less_equal_implies_less_equal(prefix, 2147483647 - count)); assumption();
 }
}
