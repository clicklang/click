import "seeded-batch.click";
import "../adler2/bounded-count.click";

// Observe the full native prefix within the shared signed specification range.
theorem zlib_full_prefix_observation(total: uint64, remaining: uint64) {
 requires to_integer(total - remaining) <= to_integer(2147483647u64);
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
 requires to_integer(total - remaining) <= to_integer(2147483647u64);
 ensures base + (total - remaining) == base + zlib_prefix_count(total, remaining) by {
  apply(adler_bounded_pointer_index(base, total - remaining));
  unfold(zlib_prefix_count(total, remaining)); assumption();
 }
}

theorem zlib_full_stream_remaining_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 2147483647u64;
 requires amount <= remaining;
 ensures to_integer(remaining - amount) <= to_integer(total) by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
 ensures to_integer(total - (remaining - amount)) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by auto(); assumption();
 }
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount) by {
  have to_integer(total - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have to_integer(remaining - amount) <= to_integer(total) by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
  have to_integer(total - (remaining - amount)) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; amount <= remaining; };
  apply(zlib_full_prefix_observation(total, remaining));
  apply(zlib_full_prefix_observation(total, remaining - amount));
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining) by auto();
  have to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount) by auto();
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by auto();
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
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by {
  apply(zlib_full_stream_remaining_step(total, remaining, amount));
  have to_integer(total - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have amount <= 2147483647u64 by arithmetic() using { amount <= remaining; remaining <= total; total <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, remaining));
  apply(zlib_full_prefix_observation(total, remaining - amount));
  apply(adler_bounded_count(amount));
  have 0 <= to_integer(total - (remaining - amount)) by auto(); have to_integer(total - (remaining - amount)) <= 18446744073709551615 by auto();
  have to_integer(total - (remaining - amount)) <= to_integer(2147483647u64) by auto();
  have to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount) >= -2147483648 by arithmetic() using { to_integer((int32)(uint32)amount) == to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount)); 0 <= to_integer(total - (remaining - amount)); };
  have to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount) <= 2147483647 by arithmetic() using { to_integer((int32)(uint32)amount) == to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount); to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount)); to_integer(total - (remaining - amount)) <= to_integer(2147483647u64); };
  have defined(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by auto();
  have to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) == to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount) by auto();
  have to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by arithmetic() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount);
   to_integer((int32)(uint32)amount) == to_integer(amount);
   to_integer(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) == to_integer(zlib_prefix_count(total, remaining)) + to_integer((int32)(uint32)amount);
  };
  assumption();
 }
}

theorem zlib_full_stream_split_count(total: uint64, middle: uint64, remaining: uint64) {
 requires remaining <= middle;
 requires middle <= total;
 requires total <= 2147483647u64;
 ensures to_integer(zlib_prefix_count(total, remaining)) == to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by {
  have remaining <= total by arithmetic() using { remaining <= middle; middle <= total; total <= 2147483647u64; };
  have middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have to_integer(total - middle) <= to_integer(2147483647u64) by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have to_integer(total - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have to_integer(middle - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= middle; middle <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, middle)); apply(zlib_full_prefix_observation(total, remaining)); apply(zlib_full_prefix_observation(middle, remaining));
  have to_integer(middle) <= to_integer(total) by auto(); have to_integer(remaining) <= to_integer(middle) by auto(); have to_integer(remaining) <= to_integer(total) by auto();
  have to_integer(total - middle) == to_integer(total) - to_integer(middle) by auto(); have to_integer(total - remaining) == to_integer(total) - to_integer(remaining) by auto(); have to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining) by auto();
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle); to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  };
  have 0 <= to_integer(total - remaining) by auto(); have to_integer(total - remaining) <= 18446744073709551615 by auto(); have to_integer(total - remaining) <= to_integer(2147483647u64) by auto();
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); 0 <= to_integer(total - remaining); };
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); to_integer(total - remaining) <= to_integer(2147483647u64); };
  have defined(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) == to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(zlib_prefix_count(total, remaining)) == to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) == to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining));
  };
  assumption();
 }
}

theorem zlib_full_stream_scalar_read_bound(total: uint64, remaining: uint64) {
 requires 1u64 <= remaining; requires remaining <= total; requires total <= 2147483647u64;
 ensures to_integer(total - remaining) < to_integer(total) by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 2147483647u64; };
 ensures to_integer(total - remaining) <= to_integer(2147483646u64) by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 2147483647u64; };
}


// A concatenation must fit its actual total, even at the signed endpoint.
theorem zlib_full_concat_bound(total: uint64, middle: uint64, remaining: uint64) {
 requires remaining <= middle; requires middle <= total; requires total <= 2147483647u64;
 ensures to_integer(zlib_prefix_count(total, middle)) <= to_integer(2147483647 - zlib_prefix_count(middle, remaining)) and defined(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by {

  have remaining <= total by arithmetic() using { remaining <= middle; middle <= total; total <= 2147483647u64; };
  have middle <= 2147483647u64 by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have to_integer(total - middle) <= to_integer(2147483647u64) by arithmetic() using { middle <= total; total <= 2147483647u64; };
  have to_integer(total - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have to_integer(middle - remaining) <= to_integer(2147483647u64) by arithmetic() using { remaining <= middle; middle <= 2147483647u64; };
  apply(zlib_full_prefix_observation(total, middle)); apply(zlib_full_prefix_observation(total, remaining)); apply(zlib_full_prefix_observation(middle, remaining));
  have to_integer(middle) <= to_integer(total) by auto(); have to_integer(remaining) <= to_integer(middle) by auto(); have to_integer(remaining) <= to_integer(total) by auto();
  have to_integer(total - middle) == to_integer(total) - to_integer(middle) by auto(); have to_integer(total - remaining) == to_integer(total) - to_integer(remaining) by auto(); have to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining) by auto();
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle); to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  };
  have 0 <= to_integer(total - remaining) by auto(); have to_integer(total - remaining) <= 18446744073709551615 by auto(); have to_integer(total - remaining) <= to_integer(2147483647u64) by auto();
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); 0 <= to_integer(total - remaining); };
  have to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) == to_integer(total - remaining); to_integer(total - remaining) <= to_integer(2147483647u64); };
  have defined(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) == to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(zlib_prefix_count(total, remaining)) == to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) by arithmetic() using {
   to_integer(zlib_prefix_count(total, middle)) == to_integer(total - middle);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(zlib_prefix_count(middle, remaining)) == to_integer(middle - remaining);
   to_integer(total - middle) == to_integer(total) - to_integer(middle);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(middle - remaining) == to_integer(middle) - to_integer(remaining);
   to_integer(zlib_prefix_count(total, middle) + zlib_prefix_count(middle, remaining)) == to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining));
  };

  have to_integer(0) <= to_integer(zlib_prefix_count(middle, remaining)) by auto();
  have zlib_prefix_count(middle, remaining) <= 2147483647 by normalize();
  have to_integer(zlib_prefix_count(middle, remaining)) <= to_integer(2147483647) by auto();
  have to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)) >= -2147483648 by arithmetic() using { to_integer(zlib_prefix_count(middle, remaining)) <= to_integer(2147483647); };
  have to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647 by arithmetic() using { to_integer(0) <= to_integer(zlib_prefix_count(middle, remaining)); };
  have defined(2147483647 - zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(2147483647 - zlib_prefix_count(middle, remaining)) == to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)) by auto();
  have to_integer(zlib_prefix_count(total, middle)) <= to_integer(2147483647 - zlib_prefix_count(middle, remaining)) by arithmetic() using { to_integer(zlib_prefix_count(total, middle)) + to_integer(zlib_prefix_count(middle, remaining)) <= 2147483647; to_integer(2147483647 - zlib_prefix_count(middle, remaining)) == to_integer(2147483647) - to_integer(zlib_prefix_count(middle, remaining)); };
  have zlib_prefix_count(total, middle) <= (2147483647 - zlib_prefix_count(middle, remaining)) by auto(); simp();
 }
}

theorem zlib_full_chunk_bound(total: uint64, remaining: uint64, amount: uint64) {
 requires amount <= remaining; requires remaining <= total; requires total <= 2147483647u64;
 ensures to_integer(zlib_prefix_count(total, remaining)) <= to_integer(2147483647 - (int32)(uint32)amount) and defined(zlib_prefix_count(total, remaining) + (int32)(uint32)amount) by {
  have remaining <= 2147483647u64 by arithmetic() using { remaining <= total; total <= 2147483647u64; };
  have to_integer(remaining - amount) <= to_integer(remaining) by arithmetic() using { amount <= remaining; remaining <= 2147483647u64; };
  apply(zlib_full_concat_bound(total, remaining, remaining - amount));
  apply(zlib_full_stream_prefix_step(remaining, remaining, amount));
  have zlib_prefix_count(remaining, remaining) == 0 by { unfold(zlib_prefix_count(remaining, remaining)); simp(); }
  have zlib_prefix_count(remaining, remaining - amount) == (int32)(uint32)amount by simp() using { to_integer(zlib_prefix_count(remaining, remaining - amount)) == to_integer(zlib_prefix_count(remaining, remaining) + (int32)(uint32)amount); zlib_prefix_count(remaining, remaining) == 0; };
  rewrite((int32)(uint32)amount == zlib_prefix_count(remaining, remaining - amount)); assumption();
 }
}

// Full-width (uint64) batch bounds, steps and joins. The object-size limit
// of the contract's 64-bit view bounds every count by 9223372036854775807.
theorem zlib_full_stream_batch_read_bound_u64(total: uint64, remaining: uint64, n: uint32) {
 requires 5552u64 <= total;
 requires total <= 9223372036854775807u64;
 requires to_integer(remaining) <= to_integer(total - 5552u64);
 requires 1u32 <= n;
 requires n <= 347u32;
 ensures remaining <= total by arithmetic() using { to_integer(remaining) <= to_integer(total - 5552u64); 5552u64 <= total; total <= 9223372036854775807u64; };
 ensures to_integer(5552u64) <= to_integer(total - remaining) by arithmetic() using { to_integer(remaining) <= to_integer(total - 5552u64); 5552u64 <= total; total <= 9223372036854775807u64; };
 ensures to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(total - 16u64) by {
  apply(zlib_batch_nonempty_remaining(n));
  apply(zlib_batch_remaining_limit(n));
  have remaining <= total by arithmetic() using { to_integer(remaining) <= to_integer(total - 5552u64); 5552u64 <= total; total <= 9223372036854775807u64; };
  have to_integer(5552u64) <= to_integer(total - remaining) by arithmetic() using { remaining <= total; to_integer(remaining) <= to_integer(total - 5552u64); 5552u64 <= total; total <= 9223372036854775807u64; };
  arithmetic() using {
   remaining <= total; to_integer(5552u64) <= to_integer(total - remaining);
   5552u64 <= total; total <= 9223372036854775807u64;
   16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64;
  };
 }
}

theorem zlib_full_native_cursor_join_u64(base: const uint8*, first: uint64, second: uint64) {
 requires to_integer(first) + to_integer(second) <= 18446744073709551615;
 ensures base + first + second == base + (first + second) by {
  have to_integer(first + second) == to_integer(first) + to_integer(second) by auto();
  normalize() using { to_integer(first + second) == to_integer(first) + to_integer(second); };
 }
}

theorem zlib_full_stream_batch_lane_bound_u64(total: uint64, remaining: uint64, n: uint32, lane: uint64) {
 requires 5552u64 <= total;
 requires total <= 9223372036854775807u64;
 requires to_integer(remaining) <= to_integer(total - 5552u64);
 requires 1u32 <= n;
 requires n <= 347u32;
 requires lane <= 15u64;
 ensures to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane) < to_integer(total) by {
  apply(zlib_full_stream_batch_read_bound_u64(total, remaining, n));
  apply(zlib_batch_remaining_limit(n));
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(9223372036854775807u64) by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(total - 16u64);
   remaining <= total; to_integer(5552u64) <= to_integer(total - remaining);
   5552u64 <= total; total <= 9223372036854775807u64; zlib_batch_remaining(n) <= 5552u64;
  };
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane) <= 18446744073709551615 by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(9223372036854775807u64); to_integer(lane) <= to_integer(15u64);
  };
  have to_integer(((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + lane) == to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane) by auto();
  have to_integer(16u64) <= to_integer(total) by arithmetic() using { to_integer(5552u64) <= to_integer(total); };
  have to_integer(total - 16u64) == to_integer(total) - to_integer(16u64) by auto();
  have to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane) < to_integer(total) by arithmetic() using {
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n)) + lane) == to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) + to_integer(lane);
   to_integer((total - remaining - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(total - 16u64);
   to_integer(total - 16u64) == to_integer(total) - to_integer(16u64);
   to_integer(lane) <= to_integer(15u64);
  };
  assumption();
 }
}

theorem zlib_full_stream_remaining_step_u64(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 9223372036854775807u64;
 requires amount <= remaining;
 ensures to_integer(remaining - amount) <= to_integer(total) by arithmetic() using { remaining <= total; total <= 9223372036854775807u64; amount <= remaining; };
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by auto(); assumption();
 }
}

// The completed prefix grows by the consumed amount, as a uint64 count.
theorem zlib_full_stream_prefix_step_u64(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires amount <= remaining;
 ensures to_integer(total - (remaining - amount)) == to_integer(total - remaining) + to_integer(amount) by {
  have to_integer(remaining - amount) <= to_integer(total) by arithmetic() using { remaining <= total; amount <= remaining; };
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining) by auto();
  have to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount) by auto();
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by auto();
  arithmetic() using {
   to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount);
  };
 }
}
theorem zlib_full_stream_prefix_sum_u64(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires amount <= remaining;
 ensures to_integer(total - (remaining - amount)) == to_integer((total - remaining) + amount) by {
  apply(zlib_full_stream_prefix_step_u64(total, remaining, amount));
  have 0 <= to_integer(total - (remaining - amount)) by auto(); have to_integer(total - (remaining - amount)) <= 18446744073709551615 by auto();
  have to_integer(total - remaining) + to_integer(amount) <= 18446744073709551615 by arithmetic() using {
   to_integer(total - (remaining - amount)) == to_integer(total - remaining) + to_integer(amount);
   to_integer(total - (remaining - amount)) <= 18446744073709551615;
  };
  have to_integer((total - remaining) + amount) == to_integer(total - remaining) + to_integer(amount) by auto();
  have to_integer(total - (remaining - amount)) == to_integer((total - remaining) + amount) by arithmetic() using {
   to_integer(total - (remaining - amount)) == to_integer(total - remaining) + to_integer(amount);
   to_integer((total - remaining) + amount) == to_integer(total - remaining) + to_integer(amount);
  };
  assumption();
 }
}

// The cursor advanced by a native amount names the longer uint64 prefix.
theorem zlib_full_prefix_advance_u64(base: const uint8*, total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires amount <= remaining;
 ensures base + (total - remaining) + amount == base + (total - (remaining - amount)) by {
  apply(zlib_full_stream_prefix_step_u64(total, remaining, amount));
  normalize() using { to_integer(total - (remaining - amount)) == to_integer(total - remaining) + to_integer(amount); };
 }
}

theorem zlib_full_stream_capacity_step_u64(n: uint32, remaining: uint64) {
 requires 1u32 <= n;
 requires n <= 347u32;
 requires remaining <= 9223372036854770255u64;
 ensures to_integer(16u64 * (uint64)n + remaining) <= to_integer(9223372036854775807u64)
     and to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)n + remaining - 16u64)
     and to_integer(16u64 * (uint64)(n - 1u32) + remaining) <= to_integer(9223372036854775807u64) by {
  have to_integer(n - 1u32) == to_integer(n) - to_integer(1u32) by auto(); apply(zlib_batch_predecessor(n));
  apply(zlib_batch_native_capacity_observation(n)); apply(zlib_batch_native_capacity_observation(n - 1u32));
  have to_integer(16u64 * (uint64)n) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); to_integer(n) <= 347; };
  have to_integer(16u64 * (uint64)(n - 1u32)) <= 5552 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32); to_integer(n - 1u32) <= 347; };
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n) by arithmetic() using { to_integer(16u64 * (uint64)n) == 16 * to_integer(n); 1 <= to_integer(n); };
  have to_integer(16u64 * (uint64)n) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 9223372036854770255; };
  have to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining) <= 18446744073709551615 by arithmetic() using { to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 9223372036854770255; };
  have to_integer((16u64 * (uint64)n) + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining) by auto(); have to_integer((16u64 * (uint64)(n - 1u32)) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining) by auto();
  have to_integer(16u64 * (uint64)n + remaining) <= to_integer(9223372036854775807u64) by arithmetic() using {
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
   to_integer(16u64 * (uint64)n) <= 5552; to_integer(remaining) <= 9223372036854770255;
  };
  have to_integer(16u64 * (uint64)(n - 1u32) + remaining) <= to_integer(9223372036854775807u64) by arithmetic() using {
   to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining);
   to_integer(16u64 * (uint64)(n - 1u32)) <= 5552; to_integer(remaining) <= 9223372036854770255;
  };
  have to_integer(16u64) <= to_integer(16u64 * (uint64)n + remaining) by arithmetic() using {
   to_integer(16u64) <= to_integer(16u64 * (uint64)n); 0 <= to_integer(remaining);
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
  };
  have to_integer((16u64 * (uint64)n + remaining) - 16u64) == to_integer(16u64 * (uint64)n + remaining) - to_integer(16u64) by auto();
  have to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)n + remaining - 16u64) by arithmetic() using {
   to_integer(16u64 * (uint64)n) == 16 * to_integer(n);
   to_integer(16u64 * (uint64)(n - 1u32)) == 16 * to_integer(n - 1u32);
   to_integer(n - 1u32) == to_integer(n) - to_integer(1u32);
   to_integer(16u64 * (uint64)n + remaining) == to_integer(16u64 * (uint64)n) + to_integer(remaining);
   to_integer(16u64 * (uint64)(n - 1u32) + remaining) == to_integer(16u64 * (uint64)(n - 1u32)) + to_integer(remaining);
   to_integer(16u64 * (uint64)n + remaining - 16u64) == to_integer(16u64 * (uint64)n + remaining) - to_integer(16u64);
  };
  simp();
 }
}

theorem zlib_full_stream_tail_read_bound_u64(total: uint64, remaining: uint64, lane: uint64) {
 requires remaining <= total;
 requires total <= 9223372036854775807u64;
 requires 16u64 <= remaining;
 requires lane <= 15u64;
 ensures to_integer(total - remaining) <= to_integer(9223372036854775791u64) by arithmetic() using { remaining <= total; total <= 9223372036854775807u64; 16u64 <= remaining; };
 ensures to_integer(total - remaining + lane) < to_integer(total) by arithmetic() using { remaining <= total; total <= 9223372036854775807u64; 16u64 <= remaining; lane <= 15u64; };
}

theorem zlib_full_stream_scalar_read_bound_u64(total: uint64, remaining: uint64) {
 requires 1u64 <= remaining; requires remaining <= total; requires total <= 9223372036854775807u64;
 ensures to_integer(total - remaining) < to_integer(total) by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 9223372036854775807u64; };
 ensures to_integer(total - remaining) <= to_integer(9223372036854775806u64) by arithmetic() using { 1u64 <= remaining; remaining <= total; total <= 9223372036854775807u64; };
}

// A batch counted by an int32 index joins the uint64 prefix it follows.
// The batch keeps its int32 sums; its length is bridged at the join.
theorem zlib_seeded_batch_concat_u64(bytes: uint8[], prefix: uint64, length: int32, count: uint64, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires to_integer(length) == to_integer(count);
 requires to_integer(prefix) + to_integer(count) <= 18446744073709551615;
 requires to_integer(a0) == adler_spec_a_u64(bytes, prefix, 1);
 requires to_integer(b0) == adler_spec_b_u64(bytes, prefix, 1, 0);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a_u64(bytes, prefix + count, 1) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_a_bridge(bytes + prefix, length, count, to_integer(a0)));
  apply(adler_spec_a_concat_u64(bytes, prefix, count, 1));
  have to_integer(a % 65521u64) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1)) by {
   rewrite(adler_spec_a_u64(bytes, prefix, 1) == to_integer(a0));
   arithmetic() using {
    to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, to_integer(a0));
    adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a_u64(bytes + prefix, count, to_integer(a0));
   };
  }
  arithmetic() using {
   to_integer(a % 65521u64) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1));
   adler_spec_a_u64(bytes, prefix + count, 1) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1));
  };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b_u64(bytes, prefix + count, 1, 0) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(adler_spec_b_bridge(bytes + prefix, length, count, to_integer(a0), to_integer(b0)));
  apply(adler_spec_b_concat_u64(bytes, prefix, count, 1, 0));
  have to_integer(b % 65521u64) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0)) by {
   rewrite(adler_spec_a_u64(bytes, prefix, 1) == to_integer(a0));
   rewrite(adler_spec_b_u64(bytes, prefix, 1, 0) == to_integer(b0));
   arithmetic() using {
    to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0));
    adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b_u64(bytes + prefix, count, to_integer(a0), to_integer(b0));
   };
  }
  arithmetic() using {
   to_integer(b % 65521u64) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0));
   adler_spec_b_u64(bytes, prefix + count, 1, 0) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0));
  };
 }
}

// The scalar tail joins an unreduced seed to the uint64 prefix it follows.
theorem zlib_raw_seeded_batch_concat_u64(bytes: uint8[], prefix: uint64, length: int32, count: uint64, a: uint64, b: uint64, a0: uint64, b0: uint64) {
 requires 0 <= length;
 requires to_integer(length) == to_integer(count);
 requires to_integer(prefix) + to_integer(count) <= 18446744073709551615;
 requires a0 <= 1500000u64;
 requires to_integer(a0 % 65521u64) == adler_spec_a_u64(bytes, prefix, 1);
 requires to_integer(b0 % 65521u64) == adler_spec_b_u64(bytes, prefix, 1, 0);
 requires to_integer(a) == to_integer(a0) + adler_byte_sum(bytes + prefix, length);
 requires to_integer(b) == to_integer(b0) + to_integer(length) * to_integer(a0) + adler_weighted_sum(bytes + prefix, length, length);
 ensures to_integer(a % 65521u64) == adler_spec_a_u64(bytes, prefix + count, 1) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_remainder_to_integer(a0, 65521u64));
  apply(adler_sum_nonnegative(bytes + prefix, length));
  apply(adler_residue_add_left(to_integer(a0), adler_byte_sum(bytes + prefix, length)));
  have adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)) by {
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0)));
   unfold(adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)));
   rewrite(to_integer(a0 % 65521u64) == truncating_remainder(to_integer(a0), 65521)); assumption();
  }
  apply(adler_spec_a_bridge(bytes + prefix, length, count, to_integer(a0 % 65521u64)));
  have to_integer(a % 65521u64) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1)) by {
   rewrite(adler_spec_a_u64(bytes, prefix, 1) == to_integer(a0 % 65521u64));
   arithmetic() using {
    to_integer(a % 65521u64) == adler_spec_a(bytes + prefix, length, to_integer(a0));
    adler_spec_a(bytes + prefix, length, to_integer(a0)) == adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64));
    adler_spec_a(bytes + prefix, length, to_integer(a0 % 65521u64)) == adler_spec_a_u64(bytes + prefix, count, to_integer(a0 % 65521u64));
   };
  }
  apply(adler_spec_a_concat_u64(bytes, prefix, count, 1));
  arithmetic() using { to_integer(a % 65521u64) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1)); adler_spec_a_u64(bytes, prefix + count, 1) == adler_spec_a_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1)); };
 }
 ensures to_integer(b % 65521u64) == adler_spec_b_u64(bytes, prefix + count, 1, 0) by {
  apply(zlib_seeded_reduced_components(bytes + prefix, length, a, b, a0, b0));
  apply(uint64_remainder_to_integer(a0, 65521u64)); apply(uint64_remainder_to_integer(b0, 65521u64));
  apply(adler_weighted_nonnegative(bytes + prefix, length));
  have length <= 2147483647 by normalize();
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
  apply(adler_spec_b_bridge(bytes + prefix, length, count, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)));
  have to_integer(b % 65521u64) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0)) by {
   rewrite(adler_spec_a_u64(bytes, prefix, 1) == to_integer(a0 % 65521u64));
   rewrite(adler_spec_b_u64(bytes, prefix, 1, 0) == to_integer(b0 % 65521u64));
   arithmetic() using {
    to_integer(b % 65521u64) == adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0));
    adler_spec_b(bytes + prefix, length, to_integer(a0), to_integer(b0)) == adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64));
    adler_spec_b(bytes + prefix, length, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64)) == adler_spec_b_u64(bytes + prefix, count, to_integer(a0 % 65521u64), to_integer(b0 % 65521u64));
   };
  }
  apply(adler_spec_b_concat_u64(bytes, prefix, count, 1, 0));
  arithmetic() using { to_integer(b % 65521u64) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0)); adler_spec_b_u64(bytes, prefix + count, 1, 0) == adler_spec_b_u64(bytes + prefix, count, adler_spec_a_u64(bytes, prefix, 1), adler_spec_b_u64(bytes, prefix, 1, 0)); };
 }
}

theorem zlib_components_pack_u64(bytes: uint8[], length: uint64, a: uint64, b: uint64) {
 requires to_integer(a % 65521u64) == adler_spec_a_u64(bytes, length, 1);
 requires to_integer(b % 65521u64) == adler_spec_b_u64(bytes, length, 1, 0);
 ensures to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == adler_spec_checksum_u64(bytes, length, 1, 0) by {
  apply(uint64_remainder_to_integer(a, 65521u64));
  apply(uint64_remainder_to_integer(b, 65521u64));
  apply(integer_positive_divisor_remainder_upper(to_integer(a), 65521));
  apply(integer_positive_divisor_remainder_upper(to_integer(b), 65521));
  have to_integer(a % 65521u64) <= 65535 by arithmetic() using {
   to_integer(a % 65521u64) == truncating_remainder(to_integer(a), 65521);
   truncating_remainder(to_integer(a), 65521) <= to_integer(65521 - 1);
  };
  have to_integer(b % 65521u64) <= 65535 by arithmetic() using {
   to_integer(b % 65521u64) == truncating_remainder(to_integer(b), 65521);
   truncating_remainder(to_integer(b), 65521) <= to_integer(65521 - 1);
  };
  apply(uint64_pack_uint16_to_integer(a % 65521u64, b % 65521u64));
  unfold(adler_spec_checksum_u64(bytes, length, 1, 0));
  arithmetic() using {
   to_integer((a % 65521u64) | ((b % 65521u64) << 16)) == to_integer(a % 65521u64) + 65536 * to_integer(b % 65521u64);
   to_integer(a % 65521u64) == adler_spec_a_u64(bytes, length, 1);
   to_integer(b % 65521u64) == adler_spec_b_u64(bytes, length, 1, 0);
  };
 }
}

// Packing order for the original one-byte path.
theorem zlib_full_pack_order(value: Integer) {
 ensures value + 65536 * value == 65536 * value + value by { arithmetic() using {}; }
}
