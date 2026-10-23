import "window.click";
function zlib_batch_remaining(n: uint32) -> uint64 { 16u64 * (uint64)n }
function zlib_batch_count(n: uint32) -> int32 { zlib_prefix_count(5552u64, zlib_batch_remaining(n)) }
theorem zlib_batch_count_bounds(n: uint32) {
 requires n <= 347u32;
 ensures to_integer((int32)n) == to_integer(n) by {
  have 0 <= to_integer(n) by auto(); have to_integer(n) <= 4294967295 by auto();
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 347 => to_integer(n) <= 347;
   integer_cast_identity bounds [0, 1] => to_integer((int32)n) == to_integer(n);
   conclusion 0;
  }
 }
 ensures 0 <= (int32)n and (int32)n <= 347 by {
  have 0 <= to_integer(n) by auto(); have to_integer(n) <= 4294967295 by auto();
  have to_integer((int32)n) == to_integer(n) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 347 => to_integer(n) <= 347;
   integer_cast_identity bounds [0, 1] => to_integer((int32)n) == to_integer(n); conclusion 0;
  } }
  have 0 <= to_integer((int32)n) by arithmetic() using { 0 <= to_integer(n); to_integer((int32)n) == to_integer(n); };
  have to_integer((int32)n) <= 347 by arithmetic() using { to_integer(n) <= 347; to_integer((int32)n) == to_integer(n); };
  simp();
 }
}
theorem zlib_batch_native_capacity_observation(n: uint32) {
 requires n <= 347u32;
 ensures to_integer(16u64 * (uint64)n) == 16 * to_integer(n) by {
  have 0 <= to_integer(n) by auto(); have to_integer(n) <= 4294967295 by auto();
  have to_integer((uint64)n) == to_integer(n) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 347 => to_integer(n) <= 347;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)n) == to_integer(n); conclusion 0;
  } }
  have to_integer(16u64) * to_integer((uint64)n) <= 18446744073709551615 by arithmetic() using { to_integer(n) <= 347; to_integer((uint64)n) == to_integer(n); };
  apply(integer::uint64_multiply_to_integer(16u64, (uint64)n));
  arithmetic() using { to_integer(16u64 * (uint64)n) == to_integer(16u64) * to_integer((uint64)n); to_integer((uint64)n) == to_integer(n); };
 }
}
theorem zlib_batch_remaining_bounds(n: uint32) {
 requires n <= 347u32;
 ensures to_integer(zlib_batch_remaining(n)) == 16 * to_integer(n) by {
  have 0 <= to_integer(n) by auto(); have to_integer(n) <= 4294967295 by auto();
  have to_integer((uint64)n) == to_integer(n) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(n) => 0 <= to_integer(n);
   premise 1: to_integer(n) <= 347 => to_integer(n) <= 347;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)n) == to_integer(n); conclusion 0;
  } }
  have to_integer(16u64) * to_integer((uint64)n) <= 18446744073709551615 by arithmetic() using { to_integer(n) <= 347; to_integer((uint64)n) == to_integer(n); };
  apply(integer::uint64_multiply_to_integer(16u64, (uint64)n));
  unfold(zlib_batch_remaining(n));
  arithmetic() using { to_integer(16u64 * (uint64)n) == to_integer(16u64) * to_integer((uint64)n); to_integer((uint64)n) == to_integer(n); };
 }
}
theorem zlib_batch_remaining_limit(n: uint32) {
 requires n <= 347u32;
 ensures zlib_batch_remaining(n) <= 5552u64 by {
  apply(zlib_batch_remaining_bounds(n));
  have to_integer(zlib_batch_remaining(n)) <= 5552 by arithmetic() using { to_integer(zlib_batch_remaining(n)) == 16 * to_integer(n); to_integer(n) <= 347; };
  assumption();
 }
}
theorem zlib_batch_prefix_observation(n: uint32) {
 requires n <= 347u32;
 ensures to_integer(zlib_batch_count(n)) == 5552 - 16 * to_integer(n) by {
  apply(zlib_batch_remaining_bounds(n));
  apply(zlib_batch_remaining_limit(n));
  have to_integer(5552u64 - zlib_batch_remaining(n)) == to_integer(5552u64) - to_integer(zlib_batch_remaining(n)) by auto();
  have 0 <= to_integer(zlib_batch_remaining(n)) by auto(); have to_integer(zlib_batch_remaining(n)) <= 18446744073709551615 by auto();
  have to_integer(5552u64 - zlib_batch_remaining(n)) <= 22208 by arithmetic() using { to_integer(5552u64 - zlib_batch_remaining(n)) == to_integer(5552u64) - to_integer(zlib_batch_remaining(n)); 0 <= to_integer(zlib_batch_remaining(n)); };
  apply(zlib_prefix_observation(5552u64, zlib_batch_remaining(n)));
  unfold(zlib_batch_count(n));
  arithmetic() using { to_integer(zlib_prefix_count(5552u64, zlib_batch_remaining(n))) == to_integer(5552u64 - zlib_batch_remaining(n)); to_integer(5552u64 - zlib_batch_remaining(n)) == to_integer(5552u64) - to_integer(zlib_batch_remaining(n)); to_integer(zlib_batch_remaining(n)) == 16 * to_integer(n); };
 }
}
theorem zlib_batch_prefix_limit(n: uint32) {
 requires n <= 347u32;
 ensures 0 <= zlib_batch_count(n) and zlib_batch_count(n) <= 5552 by {
  apply(zlib_batch_prefix_observation(n));
  have 0 <= to_integer(n) by auto(); have to_integer(n) <= 4294967295 by auto();
  have 0 <= to_integer(zlib_batch_count(n)) by arithmetic() using { to_integer(zlib_batch_count(n)) == 5552 - 16 * to_integer(n); to_integer(n) <= 347; };
  have to_integer(zlib_batch_count(n)) <= 5552 by arithmetic() using { to_integer(zlib_batch_count(n)) == 5552 - 16 * to_integer(n); 0 <= to_integer(n); };
  simp();
 }
}
theorem zlib_batch_nonempty_prefix(n: uint32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures zlib_batch_count(n) <= 5536 by {
  apply(zlib_batch_prefix_observation(n));
  have to_integer(zlib_batch_count(n)) <= 5536 by arithmetic() using { to_integer(zlib_batch_count(n)) == 5552 - 16 * to_integer(n); to_integer(1u32) <= to_integer(n); };
  assumption();
 }
}
theorem zlib_batch_empty_components(bytes: uint8[]) {
 ensures adler_spec_a(bytes, 0, 1) == 1 and adler_spec_b(bytes, 0, 1, 0) == 0 by {
  apply(adler_sum_empty(bytes, 0));
  unfold(adler_spec_a(bytes, 0, 1));
  unfold(adler_spec_b(bytes, 0, 1, 0));
  rewrite(adler_byte_sum(bytes, 0) == 0);
  rewrite(adler_weighted_sum(bytes, 0, 0) == 0); both { normalize(); } and { normalize(); }
 }
}
theorem zlib_batch_predecessor(n: uint32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures to_integer(n - 1u32) <= to_integer(347u32) by {
  have to_integer(n - 1u32) == to_integer(n) - to_integer(1u32) by auto();
  have to_integer(n - 1u32) <= 347 by arithmetic() using { to_integer(n - 1u32) == to_integer(n) - to_integer(1u32); to_integer(n) <= 347; };
  assumption();
 }
}
theorem zlib_batch_prefix_step(n: uint32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures to_integer(n - 1u32) <= to_integer(347u32) by { apply(zlib_batch_predecessor(n)); assumption(); }
 ensures zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16 by {
  apply(zlib_batch_predecessor(n));
  apply(zlib_batch_prefix_observation(n));
  apply(zlib_batch_prefix_observation(n - 1u32));
  apply(zlib_batch_nonempty_prefix(n));
  apply(zlib_batch_prefix_limit(n));
  have to_integer(n - 1u32) == to_integer(n) - to_integer(1u32) by auto();
  have defined(zlib_batch_count(n) + 16) by simp();
  have to_integer(zlib_batch_count(n) + 16) == to_integer(zlib_batch_count(n)) + to_integer(16) by auto();
  have to_integer(zlib_batch_count(n - 1u32)) == to_integer(zlib_batch_count(n) + 16) by arithmetic() using {
   to_integer(zlib_batch_count(n - 1u32)) == 5552 - 16 * to_integer(n - 1u32);
   to_integer(n - 1u32) == to_integer(n) - to_integer(1u32);
   to_integer(zlib_batch_count(n)) == 5552 - 16 * to_integer(n);
   to_integer(zlib_batch_count(n) + 16) == to_integer(zlib_batch_count(n)) + to_integer(16);
  };
  assumption();
 }
}
theorem zlib_batch_prefix_initial() {
 ensures zlib_batch_count(347u32) == 0 by {
  apply(zlib_batch_prefix_observation(347u32));
  have to_integer(zlib_batch_count(347u32)) == to_integer(0) by arithmetic() using { to_integer(zlib_batch_count(347u32)) == 5552 - 16 * to_integer(347u32); };
  assumption();
 }
}
// The sum is defined, stated apart so the observations of it in
// `zlib_batch_lane` are stated where its definedness is established.
theorem zlib_batch_lane_defined(n: uint32, lane: int32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires 0 <= lane;
 requires lane <= 15;
 ensures defined(zlib_batch_count(n) + lane) by {
  apply(zlib_batch_prefix_limit(n));
  apply(zlib_batch_nonempty_prefix(n));
  simp();
 }
}

theorem zlib_batch_lane(n: uint32, lane: int32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires 0 <= lane;
 requires lane <= 15;
 requires defined(zlib_batch_count(n) + lane);
 ensures 0 <= to_integer(zlib_batch_count(n) + lane) and to_integer(zlib_batch_count(n) + lane) < 5552 by {
  apply(zlib_batch_prefix_limit(n));
  apply(zlib_batch_nonempty_prefix(n));
  have to_integer(zlib_batch_count(n) + lane) == to_integer(zlib_batch_count(n)) + to_integer(lane) by auto();
  have 0 <= to_integer(zlib_batch_count(n) + lane) by arithmetic() using {
   to_integer(zlib_batch_count(n) + lane) == to_integer(zlib_batch_count(n)) + to_integer(lane);
   0 <= to_integer(zlib_batch_count(n)); 0 <= to_integer(lane);
  };
  have to_integer(zlib_batch_count(n) + lane) <= 5551 by arithmetic() using {
   to_integer(zlib_batch_count(n) + lane) == to_integer(zlib_batch_count(n)) + to_integer(lane);
   to_integer(zlib_batch_count(n)) <= 5536; to_integer(lane) <= 15;
  };
  both { assumption(); }
  and { arithmetic() using { to_integer(zlib_batch_count(n) + lane) <= 5551; }; }
 }
}
theorem zlib_batch_cursor(base: const uint8*, n: uint32) {
 requires n <= 347u32;
 ensures base + zlib_batch_count(n) == base + (5552u64 - zlib_batch_remaining(n)) by {
  apply(zlib_batch_remaining_limit(n));
  have to_integer(5552u64 - zlib_batch_remaining(n)) == to_integer(5552u64) - to_integer(zlib_batch_remaining(n)) by auto();
  have 0 <= to_integer(zlib_batch_remaining(n)) by auto(); have to_integer(zlib_batch_remaining(n)) <= 18446744073709551615 by auto();
  have to_integer(5552u64 - zlib_batch_remaining(n)) <= 22208 by arithmetic() using { to_integer(5552u64 - zlib_batch_remaining(n)) == to_integer(5552u64) - to_integer(zlib_batch_remaining(n)); 0 <= to_integer(zlib_batch_remaining(n)); };
  apply(zlib_prefix_pointer(base, 5552u64, zlib_batch_remaining(n)));
  unfold(zlib_batch_count(n)); simp();
 }
}
theorem zlib_batch_nonempty_remaining(n: uint32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures 16u64 <= zlib_batch_remaining(n) by {
  apply(zlib_batch_remaining_bounds(n));
  have to_integer(16u64) <= to_integer(zlib_batch_remaining(n)) by arithmetic() using { to_integer(zlib_batch_remaining(n)) == 16 * to_integer(n); to_integer(1u32) <= to_integer(n); };
  assumption();
 }
}
theorem zlib_batch_read_bound(n: uint32, lane: uint64) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires lane <= 15u64;
 ensures to_integer(5552u64 - zlib_batch_remaining(n)) <= to_integer(5536u64) by {
  apply(zlib_batch_remaining_limit(n)); apply(zlib_batch_nonempty_remaining(n));
  arithmetic() using { 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
 }
 ensures to_integer(5552u64 - zlib_batch_remaining(n) + lane) < to_integer(5552u64) by {
  apply(zlib_batch_remaining_limit(n)); apply(zlib_batch_nonempty_remaining(n));
  arithmetic() using { 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; lane <= 15u64; };
 }
}

theorem zlib_batch_byte_lane(bytes: uint8[], n: uint32, lane: int32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires 0 <= lane;
 requires lane <= 15;
 ensures (bytes + zlib_batch_count(n))[lane] == bytes[zlib_batch_count(n) + lane] by {
  apply(zlib_batch_lane_defined(n, lane)); apply(zlib_batch_lane(n, lane));
  apply(zlib_batch_prefix_limit(n));
  apply(zlib_batch_nonempty_prefix(n));
  have defined(zlib_batch_count(n) + lane) by simp();
  have bytes + zlib_batch_count(n) + lane == bytes + (zlib_batch_count(n) + lane) by {
   normalize() using { defined(zlib_batch_count(n) + lane); };
  }
  simp() using { bytes + zlib_batch_count(n) + lane == bytes + (zlib_batch_count(n) + lane); };
 }
}

theorem zlib_batch_positive(n: uint32) {
 requires n != 0u32;
 ensures 1u32 <= n by {
  apply(integer::uint32_remainder_less_than_divisor(0u32, n));
  have 0 <= to_integer(0u32 % n) by auto(); have to_integer(0u32 % n) <= 4294967295 by auto();
  have 1 <= to_integer(n) by arithmetic() using { 0 <= to_integer(0u32 % n); to_integer(0u32 % n) < to_integer(n); };
  assumption();
 }
}

theorem zlib_batch_capacity_step(n: uint32) {
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures to_integer(16u64 * (uint64)(n - 1u32)) == to_integer(16u64 * (uint64)n - 16u64) by {
  apply(zlib_batch_predecessor(n));
  apply(zlib_batch_remaining_bounds(n));
  apply(zlib_batch_remaining_bounds(n - 1u32));
  apply(zlib_batch_nonempty_remaining(n));
  unfold(zlib_batch_remaining(n));
  unfold(zlib_batch_remaining(n - 1u32));
  have to_integer(n - 1u32) == to_integer(n) - to_integer(1u32) by auto();
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n) by simp();
  have to_integer((16u64 * (uint64)n) - 16u64) == to_integer(16u64 * (uint64)n) - to_integer(16u64) by auto();
  apply(zlib_batch_native_capacity_observation(n));
  apply(zlib_batch_native_capacity_observation(n - 1u32));
  have to_integer(16u64 * (uint64)(n - 1u32)) == to_integer(16u64 * (uint64)n - 16u64) by arithmetic() using {
   to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32);
   to_integer(16u64 * (uint64)n) == 16 * to_integer(n);
   to_integer(n - 1u32) == to_integer(n) - to_integer(1u32);
   to_integer(16u64 * (uint64)n - 16u64) == to_integer(16u64 * (uint64)n) - to_integer(16u64);
  };
  assumption();
 }
}

theorem zlib_batch_prefix_final() {
 ensures zlib_batch_count(0u32) == 5552 by {
  apply(zlib_batch_prefix_observation(0u32));
  have to_integer(zlib_batch_count(0u32)) == to_integer(5552) by arithmetic() using {
   to_integer(zlib_batch_count(0u32)) == 5552 - 16 * to_integer(0u32);
  };
  assumption();
 }
}

theorem zlib_batch_reduced_components(bytes: uint8[], a: uint64, b: uint64) {
 requires to_integer(a) == 1 + adler_byte_sum(bytes, 5552);
 requires to_integer(b) == to_integer(5552) + adler_weighted_sum(bytes, 5552, 5552);
 ensures to_integer(a % 65521u64) == adler_spec_a(bytes, 5552, 1) by {
  apply(integer::uint64_remainder_to_integer(a, 65521u64));
  unfold(adler_spec_a(bytes, 5552, 1));
  rewrite(1 + adler_byte_sum(bytes, 5552) == to_integer(a));
  assumption();
 }
 ensures to_integer(b % 65521u64) == adler_spec_b(bytes, 5552, 1, 0) by {
  apply(integer::uint64_remainder_to_integer(b, 65521u64));
  unfold(adler_spec_b(bytes, 5552, 1, 0));
  have 0 + to_integer(5552) * 1 + adler_weighted_sum(bytes, 5552, 5552) == to_integer(b) by arithmetic() using {
   to_integer(b) == to_integer(5552) + adler_weighted_sum(bytes, 5552, 5552);
  };
  rewrite(0 + to_integer(5552) * 1 + adler_weighted_sum(bytes, 5552, 5552) == to_integer(b));
  assumption();
 }
}
