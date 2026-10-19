import "seeded-batch.click";
import "../adler2/bounded-count.click";

// Observe the full native prefix within the shared signed specification range.
theorem zlib_full_prefix_observation(total: uint64, remaining: uint64) {
 requires total - remaining <= 2147483647u64;
 ensures to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining) by {
  apply(adler_bounded_count(total - remaining));
  unfold(zlib_prefix_count(total, remaining)); assumption();
 }
 ensures 0 <= zlib_prefix_count(total, remaining) and zlib_prefix_count(total, remaining) <= 2147483647 by {
  apply(adler_bounded_count(total - remaining));
  unfold(zlib_prefix_count(total, remaining)); simp();
 }
}
theorem zlib_full_prefix_pointer(base: const uint8*, total: uint64, remaining: uint64) {
 requires total - remaining <= 2147483647u64;
 ensures base + (total - remaining) == base + zlib_prefix_count(total, remaining) by {
  apply(adler_bounded_pointer_index(base, total - remaining));
  unfold(zlib_prefix_count(total, remaining)); assumption();
 }
}

theorem zlib_full_stream_batch_read_bound(total: uint64, remaining: uint64, n: uint32) {
 requires 5552u64 <= total;
 requires total <= 2147483647u64;
 requires remaining <= total - 5552u64;
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
 ensures 5552u64 <= total - remaining by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= total - 16u64 by {
  apply(zlib_batch_nonempty_remaining(n));
  apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  arithmetic() using {
   remaining <= total; 5552u64 <= total - remaining;
   5552u64 <= total; total <= 2147483647u64;
   16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64;
  };
 }
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) < total by {
  apply(zlib_batch_nonempty_remaining(n)); apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  arithmetic() using { remaining <= total; 5552u64 <= total - remaining; 5552u64 <= total; total <= 2147483647u64; 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
 }
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + 16u64 <= total by {
  apply(zlib_batch_nonempty_remaining(n)); apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  have 5552u64 <= total - remaining by arithmetic() using { remaining <= total; remaining <= total - 5552u64; 5552u64 <= total; total <= 2147483647u64; };
  arithmetic() using { remaining <= total; 5552u64 <= total - remaining; 5552u64 <= total; total <= 2147483647u64; 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
 }

}

theorem zlib_full_native_cursor_join(base: const uint8*, first: uint64, second: uint64) {
 requires first <= 2147483647u64;
 requires second <= 5552u64;
 requires first + second <= 2147483647u64;
 ensures base + first + second == base + (first + second) by {
  apply(uint64_less_equal_to_integer(first, 2147483647u64));
  apply(uint64_less_equal_to_integer(second, 5552u64));
  have to_integer(first) + to_integer(second) <= 18446744073709551615 by arithmetic() using {
   to_integer(first) <= to_integer(2147483647u64); to_integer(second) <= to_integer(5552u64);
  };
  apply(uint64_add_to_integer(first, second));
  have second <= 2147483647u64 by arithmetic() using { second <= 5552u64; };
  apply(adler_bounded_count(first));
  apply(adler_bounded_count(second));
  apply(adler_bounded_count(first + second));
  apply(uint64_to_integer_bounds(first)); apply(uint64_to_integer_bounds(second));
  apply(uint64_less_equal_to_integer(first + second, 2147483647u64));
  have to_integer((int32)(uint32)first) + to_integer((int32)(uint32)second) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)first) == to_integer(first); to_integer((int32)(uint32)second) == to_integer(second); 0 <= to_integer(first); 0 <= to_integer(second); };
  have to_integer((int32)(uint32)first) + to_integer((int32)(uint32)second) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)first) == to_integer(first); to_integer((int32)(uint32)second) == to_integer(second); to_integer(first + second) == to_integer(first) + to_integer(second); to_integer(first + second) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds((int32)(uint32)first, (int32)(uint32)second));
  apply(int32_add_to_integer((int32)(uint32)first, (int32)(uint32)second));
  have to_integer((int32)(uint32)(first + second)) == to_integer((int32)(uint32)first + (int32)(uint32)second) by arithmetic() using {
   to_integer((int32)(uint32)(first + second)) == to_integer(first + second);
   to_integer(first + second) == to_integer(first) + to_integer(second);
   to_integer((int32)(uint32)first) == to_integer(first);
   to_integer((int32)(uint32)second) == to_integer(second);
   to_integer((int32)(uint32)first + (int32)(uint32)second) == to_integer((int32)(uint32)first) + to_integer((int32)(uint32)second);
  };
  apply(int32_to_integer_equal_implies_equal((int32)(uint32)(first + second), (int32)(uint32)first + (int32)(uint32)second));
  apply(adler_bounded_pointer_index(base, first));
  apply(adler_bounded_pointer_index(base + first, second));
  apply(adler_bounded_pointer_index(base, first + second));
  rewrite(base + first + second == base + first + (int32)(uint32)second);
  rewrite(base + first == base + (int32)(uint32)first);
  rewrite(base + (first + second) == base + (int32)(uint32)(first + second));
  rewrite((int32)(uint32)(first + second) == (int32)(uint32)first + (int32)(uint32)second);
  normalize() using { defined((int32)(uint32)first + (int32)(uint32)second); };
 }
}

theorem zlib_full_stream_batch_lane_bound(total: uint64, remaining: uint64, n: uint32, lane: uint64) {
 requires 5552u64 <= total;
 requires total <= 2147483647u64;
 requires remaining <= total - 5552u64;
 requires 1u32 <= n;
 requires n <= 347u32;
 requires lane <= 15u64;
 ensures (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane < total by {
  apply(zlib_full_stream_batch_read_bound(total, remaining, n));
  apply(zlib_batch_remaining_limit(n));
  have (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= 2147483647u64 by arithmetic() using {
   (total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) <= total - 16u64;
   remaining <= total; 5552u64 <= total - remaining;
   5552u64 <= total; total <= 2147483647u64; zlib_batch_remaining(n) <= 5552u64;
  };
  apply(uint64_less_equal_to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)), 2147483647u64));
  apply(uint64_less_equal_to_integer(lane, 15u64));
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane) <= 18446744073709551615 by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(2147483647u64); to_integer(lane) <= to_integer(15u64);
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

theorem zlib_full_stream_remaining_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 2147483647u64;
 requires amount <= remaining;
 ensures remaining - amount <= total by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
 ensures total - (remaining - amount) <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  apply(uint64_less_equal_to_integer(amount, remaining));
  apply(uint64_subtract_to_integer(remaining, amount)); assumption();
 }
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount) by {
  have total - remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have remaining - amount <= total by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
  have total - (remaining - amount) <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
  apply(zlib_full_prefix_observation(total, remaining));
  apply(zlib_full_prefix_observation(total, remaining - amount));
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


theorem zlib_full_stream_prefix_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 2147483647u64;
 requires amount <= remaining;
 ensures zlib_prefix_count(total, remaining - amount) == zlib_prefix_count(total, remaining) + (int32)(uint32)amount by {
  apply(zlib_full_stream_remaining_step(total, remaining, amount));
  have total - remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have amount <= 2147483647u64 by arithmetic() using { amount <= remaining; remaining <= total; total <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, remaining));
  apply(zlib_full_prefix_observation(total, remaining - amount));
  apply(adler_bounded_count(amount));
  apply(uint64_to_integer_bounds(total - (remaining - amount)));
  apply(uint64_less_equal_to_integer(total - (remaining - amount), 2147483647u64));
  have to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)amount) == to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount)); 0 <= to_integer(total - (remaining - amount)); };
  have to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)amount) == to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount)); to_integer(total - (remaining - amount)) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds(zlib_prefix_count(total, remaining), (int32)(uint32)amount));
  apply(int32_add_to_integer(zlib_prefix_count(total, remaining), (int32)(uint32)amount));
  have to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount);
   to_integer((int32)(uint32)amount) == to_integer(amount);
   to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) == to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount);
  };
  apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(total, remaining - amount), zlib_prefix_count(total, remaining) + (int32)(uint32)amount)); assumption();
 }
}

theorem zlib_full_stream_capacity_step(n: uint32, remaining: uint64) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires remaining <= 2147478095u64;
 ensures 16u64 * (uint64)n + remaining <= 2147483647u64
     and 16u64 * (uint64)(n - 1u32) + remaining == 16u64 * (uint64)n + remaining - 16u64
     and 16u64 * (uint64)(n - 1u32) + remaining <= 2147483647u64 by {
  apply(uint32_less_equal_to_integer(1u32, n)); apply(uint32_less_equal_to_integer(n, 347u32));
  apply(uint32_subtract_to_integer(n, 1u32)); apply(zlib_batch_predecessor(n));
  apply(uint32_less_equal_to_integer(n - 1u32, 347u32));
  apply(zlib_batch_native_capacity_observation(n)); apply(zlib_batch_native_capacity_observation(n - 1u32));
  apply(uint64_less_equal_to_integer(remaining, 2147478095u64)); apply(uint64_to_integer_bounds(remaining));
  have to_integer(16u64 * (uint64)n) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); to_integer(n) <= 347; };
  have to_integer(16u64 * (uint64)(n - 1u32)) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32); to_integer(n - 1u32) <= 347; };
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n) by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); 1 <= to_integer(n); };
  have to_integer(16u64 * (uint64)n) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 2147478095; };
  have to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 2147478095; };
  apply(uint64_add_to_integer(16u64 * (uint64)n, remaining)); apply(uint64_add_to_integer(16u64 * (uint64)(n - 1u32), remaining));
  have to_integer(16u64 * (uint64)n + remaining) <= to_integer(2147483647u64) by arithmetic() using {
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
   to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 2147478095;
  };
  have to_integer(16u64 * (uint64)(n - 1u32) + remaining) <= to_integer(2147483647u64) by arithmetic() using {
   to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining);
   to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 2147478095;
  };
  apply(uint64_to_integer_less_equal_implies_less_equal(16u64 * (uint64)n + remaining, 2147483647u64));
  apply(uint64_to_integer_less_equal_implies_less_equal(16u64 * (uint64)(n - 1u32) + remaining, 2147483647u64));
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

theorem zlib_full_stream_tail_read_bound(total: uint64, remaining: uint64, lane: uint64) {
 requires remaining <= total;
 requires total <= 2147483647u64;
 requires 16u64 <= remaining;
 requires lane <= 15u64;
 ensures total - remaining <= 2147483631u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; 16u64 <= remaining; };
 ensures total - remaining + lane < total by arithmetic() using { remaining <= total; total <= 2147483647u64; 16u64 <= remaining; lane <= 15u64; };
}

theorem zlib_full_stream_split_count(total: uint64, middle: uint64, remaining: uint64) {
 requires remaining <= middle;
 requires middle <= total;
 requires total <= 2147483647u64;
 ensures zlib_prefix_count(total, remaining) == zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining) by {
  have remaining <= total by arithmetic() using { remaining <= middle; middle <= total; total <= 2147483647u64; };
  have middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have total - middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have total - remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have middle - remaining <= 2147483647u64 by arithmetic() using { remaining <= middle; middle <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, middle)); apply(zlib_full_prefix_observation(total, remaining)); apply(zlib_full_prefix_observation(middle, remaining));
  apply(uint64_less_equal_to_integer(middle, total)); apply(uint64_less_equal_to_integer(remaining, middle)); apply(uint64_less_equal_to_integer(remaining, total));
  apply(uint64_subtract_to_integer(total, middle)); apply(uint64_subtract_to_integer(total, remaining)); apply(uint64_subtract_to_integer(middle, remaining));
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle); to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  };
  apply(uint64_to_integer_bounds(total - remaining)); apply(uint64_less_equal_to_integer(total - remaining, 2147483647u64));
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); 0 <= to_integer(total - remaining); };
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); to_integer(total - remaining) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds(zlib_prefix_count(total, middle), zlib_prefix_count(middle, remaining)));
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

theorem zlib_full_stream_scalar_read_bound(total: uint64, remaining: uint64) {
 requires 1u64 <= remaining; requires remaining <= total; requires total <= 2147483647u64;
 ensures total - remaining < total by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 2147483647u64; };
 ensures total - remaining <= 2147483646u64 by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 2147483647u64; };
}


// A concatenation must fit its actual total, even at the signed endpoint.
theorem zlib_full_concat_bound(total: uint64, middle: uint64, remaining: uint64) {
 requires remaining <= middle; requires middle <= total; requires total <= 2147483647u64;
 ensures zlib_prefix_count(total, middle) <= 2147483647 - zlib_prefix_count(middle, remaining) and defined(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by {

  have remaining <= total by arithmetic() using { remaining <= middle; middle <= total; total <= 2147483647u64; };
  have middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have total - middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have total - remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have middle - remaining <= 2147483647u64 by arithmetic() using { remaining <= middle; middle <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, middle)); apply(zlib_full_prefix_observation(total, remaining)); apply(zlib_full_prefix_observation(middle, remaining));
  apply(uint64_less_equal_to_integer(middle, total)); apply(uint64_less_equal_to_integer(remaining, middle)); apply(uint64_less_equal_to_integer(remaining, total));
  apply(uint64_subtract_to_integer(total, middle)); apply(uint64_subtract_to_integer(total, remaining)); apply(uint64_subtract_to_integer(middle, remaining));
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle); to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  };
  apply(uint64_to_integer_bounds(total - remaining)); apply(uint64_less_equal_to_integer(total - remaining, 2147483647u64));
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); 0 <= to_integer(total - remaining); };
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); to_integer(total - remaining) <= to_integer(2147483647u64); };
  apply(int32_add_defined_by_integer_bounds(zlib_prefix_count(total, middle), zlib_prefix_count(middle, remaining)));
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
  apply(int32_to_integer_equal_implies_equal(zlib_prefix_count(total, remaining), zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)));

  apply(int32_less_equal_to_integer(0, zlib_prefix_count(middle, remaining)));
  have zlib_prefix_count(middle, remaining) <= 2147483647 by normalize();
  apply(int32_less_equal_to_integer(zlib_prefix_count(middle, remaining), 2147483647));
  have to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(middle, remaining)) <= to_integer(2147483647); };
  have to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(0) <= to_integer(zlib_prefix_count(middle, remaining)); };
  apply(int32_subtract_defined_by_integer_bounds(2147483647, zlib_prefix_count(middle, remaining)));
  apply(int32_subtract_to_integer(2147483647, zlib_prefix_count(middle, remaining)));
  have to_integer(zlib_prefix_count(total, middle)) <= to_integer(2147483647 - zlib_prefix_count(middle, remaining)) by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647; to_integer(2147483647 - zlib_prefix_count(middle, remaining)) == to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)); };
  apply(int32_to_integer_less_equal_implies_less_equal(zlib_prefix_count(total, middle), 2147483647 - zlib_prefix_count(middle, remaining))); simp();
 }
}

theorem zlib_full_chunk_bound(total: uint64, remaining: uint64, amount: uint64) {
 requires amount <= remaining; requires remaining <= total; requires total <= 2147483647u64;
 ensures zlib_prefix_count(total, remaining) <= 2147483647 - (int32)(uint32)amount and defined(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by {
  have remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have remaining - amount <= remaining by arithmetic() using { amount <= remaining; remaining <= 2147483647u64; };
  apply(zlib_full_concat_bound(total, remaining, remaining - amount));
  apply(zlib_full_stream_prefix_step(remaining, remaining, amount));
  have zlib_prefix_count(remaining, remaining) == 0 by { unfold(zlib_prefix_count(remaining, remaining)); simp(); }
  have zlib_prefix_count(remaining, remaining - amount) == (int32)(uint32)amount by simp() using { zlib_prefix_count(remaining, remaining - amount) == zlib_prefix_count(remaining, remaining) + (int32)(uint32)amount; zlib_prefix_count(remaining, remaining) == 0; };
  rewrite((int32)(uint32)amount == zlib_prefix_count(remaining, remaining - amount)); assumption();
 }
}

// Packing order for the original one-byte path.
theorem zlib_full_pack_order(value: Integer) {
 ensures value + 65536 * value == 65536 * value + value by { arithmetic() using {}; }
}
