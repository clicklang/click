# The 32-bit view of a 64-bit iterator count.
# A chunk iterator counts its remaining bytes as `usize`. The lane and tail
# bound libraries state their ceilings over an `int32` count; within one
# batch the count is at most 22208, where the view `(int32)(uint32)count`
# is the count itself. These carry the iterator's 64-bit facts to that view.

theorem adler_count_observation(r: uint64) {
 requires r <= 22208u64;
 ensures to_integer((int32)(uint32)r) == to_integer(r) by {
  have 0u64 <= r by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, r)) using { 0u64 <= r; }
  apply(uint64_less_equal_to_integer(r, 22208u64)) using { r <= 22208u64; }
  arithmetic_certificate special {
   premise 0: 0 <= to_integer(r) => 0 <= to_integer(r);
   premise 1: to_integer(r) <= 22208 => to_integer(r) <= 22208;
   integer_cast_identity bounds [0, 1] => to_integer((int32)(uint32)r) == to_integer(r);
   conclusion 0;
  }
 }
}
theorem adler_count_bounds(r: uint64) {
 requires r <= 22208u64;
 ensures 0 <= (int32)(uint32)r and (int32)(uint32)r <= 22208 by {
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  have 0u64 <= r by { normalize(); }
  apply(uint64_less_equal_to_integer(0u64, r)) using { 0u64 <= r; }
  apply(uint64_less_equal_to_integer(r, 22208u64)) using { r <= 22208u64; }
  have 0 <= to_integer((int32)(uint32)r) by { rewrite(to_integer((int32)(uint32)r) == to_integer(r)); assumption(); }
  have to_integer((int32)(uint32)r) <= 22208 by { rewrite(to_integer((int32)(uint32)r) == to_integer(r)); assumption(); }
  both {
   apply(int32_less_equal_of_to_integer(0, (int32)(uint32)r)) using { 0 <= to_integer((int32)(uint32)r); }
  } and {
   apply(int32_less_equal_of_to_integer((int32)(uint32)r, 22208)) using { to_integer((int32)(uint32)r) <= 22208; }
  }
 }
}
theorem adler_count_at_least(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures (int32)(uint32)k <= (int32)(uint32)r by {
  have k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  apply(adler_count_observation(k)) using { k <= 22208u64; }
  apply(uint64_less_equal_to_integer(k, r)) using { k <= r; }
  have to_integer((int32)(uint32)k) <= to_integer((int32)(uint32)r) by {
   rewrite(to_integer((int32)(uint32)k) == to_integer(k));
   rewrite(to_integer((int32)(uint32)r) == to_integer(r));
   assumption();
  }
  apply(int32_less_equal_of_to_integer((int32)(uint32)k, (int32)(uint32)r)) using { to_integer((int32)(uint32)k) <= to_integer((int32)(uint32)r); }
 }
}
theorem adler_count_step(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures (int32)(uint32)(r - k) == (int32)(uint32)r - (int32)(uint32)k by {
  have k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  have r - k <= 22208u64 by { arithmetic() using { k <= r; r <= 22208u64; } }
  apply(adler_count_observation(r)) using { r <= 22208u64; }
  apply(adler_count_observation(k)) using { k <= 22208u64; }
  apply(adler_count_observation(r - k)) using { r - k <= 22208u64; }
  apply(adler_count_bounds(r)) using { r <= 22208u64; }
  apply(adler_count_bounds(k)) using { k <= 22208u64; }
  apply(adler_count_at_least(r, k)) using { k <= r; r <= 22208u64; }
  apply(uint64_less_equal_to_integer(k, r)) using { k <= r; }
  apply(uint64_subtract_to_integer(r, k)) using { to_integer(k) <= to_integer(r); }
  apply(int32_nonnegative_subtract_within_value_is_defined((int32)(uint32)r, (int32)(uint32)k)) using { 0 <= (int32)(uint32)k; (int32)(uint32)k <= (int32)(uint32)r; }
  apply(int32_subtract_to_integer((int32)(uint32)r, (int32)(uint32)k)) using { defined((int32)(uint32)r - (int32)(uint32)k); }
  have to_integer((int32)(uint32)(r - k)) == to_integer((int32)(uint32)r - (int32)(uint32)k) by {
   rewrite(to_integer((int32)(uint32)(r - k)) == to_integer(r - k));
   rewrite(to_integer(r - k) == to_integer(r) - to_integer(k));
   rewrite(to_integer((int32)(uint32)r - (int32)(uint32)k) == to_integer((int32)(uint32)r) - to_integer((int32)(uint32)k));
   rewrite(to_integer((int32)(uint32)r) == to_integer(r));
   rewrite(to_integer((int32)(uint32)k) == to_integer(k));
   normalize();
  }
  apply(int32_equal_of_to_integer((int32)(uint32)(r - k), (int32)(uint32)r - (int32)(uint32)k)) using { to_integer((int32)(uint32)(r - k)) == to_integer((int32)(uint32)r - (int32)(uint32)k); }
 }
}
theorem adler_count_lane_step(r: uint64) {
 requires 4u64 <= r;
 requires r <= 22208u64;
 ensures 4 <= (int32)(uint32)r by {
  apply(adler_count_at_least(r, 4u64)) using { 4u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)4u64 <= (int32)(uint32)r; }
 }
 ensures (int32)(uint32)(r - 4u64) == (int32)(uint32)r - 4 by {
  apply(adler_count_step(r, 4u64)) using { 4u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)(r - 4u64) == (int32)(uint32)r - (int32)(uint32)4u64; }
 }
}
theorem adler_count_tail_step(r: uint64) {
 requires 1u64 <= r;
 requires r <= 22208u64;
 ensures 1 <= (int32)(uint32)r by {
  apply(adler_count_at_least(r, 1u64)) using { 1u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)1u64 <= (int32)(uint32)r; }
 }
 ensures (int32)(uint32)(r - 1u64) == (int32)(uint32)r - 1 by {
  apply(adler_count_step(r, 1u64)) using { 1u64 <= r; r <= 22208u64; }
  normalize() using { (int32)(uint32)(r - 1u64) == (int32)(uint32)r - (int32)(uint32)1u64; }
 }
}
