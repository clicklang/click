import click::integer;

// The 32-bit view of a 64-bit iterator count.
// A chunk iterator counts its remaining bytes as `usize`. The lane and tail
// bound libraries state their ceilings over an `int32` count; within one
// batch the count is at most 22208, where the view `count as uint32 as int32`
// is the count itself. These carry the iterator's 64-bit facts to that view.

theorem adler_count_observation(r: uint64) {
 requires r <= 22208u64;
 ensures to_integer(r as uint32 as int32) == to_integer(r) by {
  have 0u64 <= r by normalize();
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(r) => 0 <= to_integer(r);
   premise 1: to_integer(r) <= 22208 => to_integer(r) <= 22208;
   integer_cast_identity bounds [0, 1] => to_integer(r as uint32 as int32) == to_integer(r);
   conclusion 0;
  }
 }
}
theorem adler_count_bounds(r: uint64) {
 requires r <= 22208u64;
 ensures 0 <= r as uint32 as int32 and r as uint32 as int32 <= 22208 by {
  apply(adler_count_observation(r)) using { r <= 22208u64; };
  have 0u64 <= r by normalize();
  have 0 <= to_integer(r as uint32 as int32) by { rewrite(to_integer(r as uint32 as int32) == to_integer(r)); assumption(); }
  have to_integer(r as uint32 as int32) <= 22208 by { rewrite(to_integer(r as uint32 as int32) == to_integer(r)); assumption(); }
  both {
   assumption();
  } and {
   assumption();
  }
 }
}
theorem adler_count_at_least(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures k as uint32 as int32 <= r as uint32 as int32 by {
  have k <= 22208u64 by solve() using { k <= r; r <= 22208u64; };
  apply(adler_count_observation(r)) using { r <= 22208u64; };
  apply(adler_count_observation(k)) using { k <= 22208u64; };
  have to_integer(k as uint32 as int32) <= to_integer(r as uint32 as int32) by {
   rewrite(to_integer(k as uint32 as int32) == to_integer(k));
   rewrite(to_integer(r as uint32 as int32) == to_integer(r));
   assumption();
  }
  assumption();
 }
}
theorem adler_count_step(r: uint64, k: uint64) {
 requires k <= r;
 requires r <= 22208u64;
 ensures to_integer((r - k) as uint32 as int32) == to_integer(r as uint32 as int32 - k as uint32 as int32) by {
  have k <= 22208u64 by solve() using { k <= r; r <= 22208u64; };
  have to_integer(r - k) <= to_integer(22208u64) by solve() using { k <= r; r <= 22208u64; };
  apply(adler_count_observation(r)) using { r <= 22208u64; };
  apply(adler_count_observation(k)) using { k <= 22208u64; };
  apply(adler_count_observation(r - k)) using { to_integer(r - k) <= to_integer(22208u64); };
  apply(adler_count_bounds(r)) using { r <= 22208u64; };
  apply(adler_count_bounds(k)) using { k <= 22208u64; };
  apply(adler_count_at_least(r, k)) using { k <= r; r <= 22208u64; };
  have to_integer(r - k) == to_integer(r) - to_integer(k);
  have to_integer((r as uint32 as int32) - (k as uint32 as int32)) == to_integer((r as uint32 as int32)) - to_integer((k as uint32 as int32));
  have to_integer((r - k) as uint32 as int32) == to_integer(r as uint32 as int32 - k as uint32 as int32) by {
   rewrite(to_integer((r - k) as uint32 as int32) == to_integer(r - k));
   rewrite(to_integer(r - k) == to_integer(r) - to_integer(k));
   rewrite(to_integer(r as uint32 as int32 - k as uint32 as int32) == to_integer(r as uint32 as int32) - to_integer(k as uint32 as int32));
   rewrite(to_integer(r as uint32 as int32) == to_integer(r));
   rewrite(to_integer(k as uint32 as int32) == to_integer(k));
   normalize();
  }
  assumption();
 }
}
theorem adler_count_lane_step(r: uint64) {
 requires 4u64 <= r;
 requires r <= 22208u64;
 ensures 4 <= r as uint32 as int32 by {
  apply(adler_count_at_least(r, 4u64)) using { 4u64 <= r; r <= 22208u64; };
  normalize() using { 4u64 as uint32 as int32 <= r as uint32 as int32; };
 }
 ensures to_integer((r - 4u64) as uint32 as int32) == to_integer(r as uint32 as int32 - 4) by {
  apply(adler_count_step(r, 4u64)) using { 4u64 <= r; r <= 22208u64; };
  normalize() using { to_integer((r - 4u64) as uint32 as int32) == to_integer(r as uint32 as int32 - 4u64 as uint32 as int32); };
 }
}
theorem adler_count_tail_step(r: uint64) {
 requires 1u64 <= r;
 requires r <= 22208u64;
 ensures 1 <= r as uint32 as int32 by {
  apply(adler_count_at_least(r, 1u64)) using { 1u64 <= r; r <= 22208u64; };
  normalize() using { 1u64 as uint32 as int32 <= r as uint32 as int32; };
 }
 ensures to_integer((r - 1u64) as uint32 as int32) == to_integer(r as uint32 as int32 - 1) by {
  apply(adler_count_step(r, 1u64)) using { 1u64 <= r; r <= 22208u64; };
  normalize() using { to_integer((r - 1u64) as uint32 as int32) == to_integer(r as uint32 as int32 - 1u64 as uint32 as int32); };
 }
}
theorem adler_count_zero(r: uint64) {
 requires r <= 22208u64;
 requires r as uint32 as int32 == 0;
 ensures r == 0u64 by {
  apply(adler_count_observation(r)) using { r <= 22208u64; };
  have to_integer(r as uint32 as int32) == 0 by { rewrite(r as uint32 as int32 == 0); normalize(); }
  have to_integer(r) == 0 by solve() using { to_integer(r as uint32 as int32) == to_integer(r); to_integer(r as uint32 as int32) == 0; };
  have to_integer(r) == to_integer(0u64) by normalize() using { to_integer(r) == 0; };
  assumption();
 }
}

// Within the checked small-count range, the native cursor and the signed
// specification index denote exactly the same byte address.
theorem adler_count_byte_pointer(base: const uint8*, count: uint64) {
 requires count <= 22208u64;
 ensures base + count == base + count as uint32 as int32 by {
  apply(adler_count_observation(count)) using { count <= 22208u64; };
  normalize() using { to_integer(count as uint32 as int32) == to_integer(count); };
 }
}

// Read equality first, then transport the native byte into the Integer spec.
theorem adler_count_byte_observation(bytes: uint8[], count: uint64) {
 requires count <= 22208u64;
 ensures to_integer(bytes[count] as int32) == to_integer(bytes[count as uint32 as int32] as int32) by {
  apply(adler_count_byte_pointer(bytes, count)) using { count <= 22208u64; };
  have bytes[count] == bytes[count as uint32 as int32] by solve() using { bytes + count == bytes + count as uint32 as int32; };
  rewrite(bytes[count] == bytes[count as uint32 as int32]);
  normalize();
 }
}
theorem adler_count_chunk_byte_observation(bytes: uint8[], count: uint64, lane: int32) {
 requires count <= 22204u64;
 requires 0 <= lane;
 requires lane <= 3;
 ensures to_integer((bytes + count)[lane] as int32) == to_integer(bytes[count as uint32 as int32 + lane] as int32) by {
  have count <= 22208u64 by normalize() using { count <= 22204u64; };
  apply(adler_count_byte_pointer(bytes, count)) using { count <= 22208u64; };
  apply(adler_count_bounds(count)) using { count <= 22208u64; };
  have count as uint32 as int32 <= 22204;
  have defined(count as uint32 as int32 + lane);
  have bytes + count + lane == bytes + (count as uint32 as int32 + lane) by {
   rewrite(bytes + count == bytes + count as uint32 as int32);
   normalize() using { defined(count as uint32 as int32 + lane); };
  }
  have (bytes + count)[lane] == bytes[count as uint32 as int32 + lane] by solve() using { bytes + count + lane == bytes + (count as uint32 as int32 + lane); };
  rewrite((bytes + count)[lane] == bytes[count as uint32 as int32 + lane]);
  normalize();
 }
}

// After Next has consumed four bytes, recover their positions from the actual
// remaining count. No auxiliary processed count supplies the input position.
theorem adler_count_previous_chunk_byte_observation(bytes: uint8[], total: uint64, remaining: uint64, lane: int32) {
 requires remaining <= total;
 requires to_integer(4u64) <= to_integer(total - remaining);
 requires total <= 22204u64;
 requires 0 <= remaining as uint32 as int32;
 requires remaining as uint32 as int32 <= total as uint32 as int32;
 requires total as uint32 as int32 <= 22204;
 requires 0 <= lane;
 requires lane <= 3;
 ensures to_integer((bytes + (total - remaining - 4u64))[lane] as int32) == to_integer(bytes[(total as uint32 as int32 - remaining as uint32 as int32) - 4 + lane] as int32) by {
  have total <= 22208u64 by normalize() using { total <= 22204u64; };
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { remaining <= total; total <= 22204u64; };
  have to_integer(total - remaining - 4u64) <= to_integer(22204u64) by solve() using { remaining <= total; to_integer(4u64) <= to_integer(total - remaining); total <= 22204u64; };
  apply(adler_count_step(total, remaining)) using { remaining <= total; total <= 22208u64; };
  apply(adler_count_lane_step(total - remaining)) using { to_integer(4u64) <= to_integer(total - remaining); to_integer(total - remaining) <= to_integer(22208u64); };
  apply(adler_count_chunk_byte_observation(bytes, total - remaining - 4u64, lane)) using { to_integer(total - remaining - 4u64) <= to_integer(22204u64); 0 <= lane; lane <= 3; };
  have to_integer((total - remaining - 4u64) as uint32 as int32) == to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 4) by {
   rewrite(to_integer((total - remaining - 4u64) as uint32 as int32) == to_integer((total - remaining) as uint32 as int32 - 4));
   rewrite(to_integer((total - remaining) as uint32 as int32) == to_integer(total as uint32 as int32 - remaining as uint32 as int32));
   normalize();
  }
  have to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 4) == to_integer((total - remaining - 4u64) as uint32 as int32) by normalize() using { to_integer((total - remaining - 4u64) as uint32 as int32) == to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 4); };
  rewrite(to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 4) == to_integer((total - remaining - 4u64) as uint32 as int32));
  assumption();
 }
}

// Exact prefix advance used by the deferred scalar B contribution.
theorem adler_small_prefix_integer_advance(total: int32, remaining: int32) {
 requires 0 <= remaining;
 requires remaining <= total;
 requires total <= 22204;
 requires 4 <= to_integer(total - remaining);
 ensures to_integer(total - remaining) == to_integer((total - remaining) - 4) + 4 by {
  have defined(total - remaining);
  have defined(total - remaining) by assumption();
  have defined((total - remaining) - 4);
  have to_integer((total - remaining) - 4) == to_integer((total - remaining)) - to_integer(4);
  solve() using { to_integer((total - remaining) - 4) == to_integer(total - remaining) - to_integer(4); };
 }
}

// Recover the scalar byte from the actual post-Next remaining count.
theorem adler_count_previous_byte_observation(bytes: uint8[], total: uint64, remaining: uint64) {
 requires remaining <= total;
 requires to_integer(1u64) <= to_integer(total - remaining);
 requires total <= 22207u64;
 requires 0 <= remaining as uint32 as int32;
 requires remaining as uint32 as int32 <= total as uint32 as int32;
 requires total as uint32 as int32 <= 22207;
 ensures to_integer((bytes + (total - remaining - 1u64))[0] as int32) == to_integer(bytes[(total as uint32 as int32 - remaining as uint32 as int32) - 1] as int32) by {
  have total <= 22208u64 by normalize() using { total <= 22207u64; };
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { remaining <= total; total <= 22207u64; };
  have to_integer(total - remaining - 1u64) <= to_integer(22207u64) by solve() using { remaining <= total; to_integer(1u64) <= to_integer(total - remaining); total <= 22207u64; };
  apply(adler_count_step(total, remaining)) using { remaining <= total; total <= 22208u64; };
  apply(adler_count_tail_step(total - remaining)) using { to_integer(1u64) <= to_integer(total - remaining); to_integer(total - remaining) <= to_integer(22208u64); };
  have to_integer(total - remaining - 1u64) <= to_integer(22208u64) by normalize() using { to_integer(total - remaining - 1u64) <= to_integer(22207u64); };
  apply(adler_count_byte_observation(bytes, total - remaining - 1u64)) using { to_integer(total - remaining - 1u64) <= to_integer(22208u64); };
  have to_integer((total - remaining - 1u64) as uint32 as int32) == to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 1) by {
   rewrite(to_integer((total - remaining - 1u64) as uint32 as int32) == to_integer((total - remaining) as uint32 as int32 - 1));
   rewrite(to_integer((total - remaining) as uint32 as int32) == to_integer(total as uint32 as int32 - remaining as uint32 as int32));
   normalize();
  }
  have to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 1) == to_integer((total - remaining - 1u64) as uint32 as int32) by normalize() using { to_integer((total - remaining - 1u64) as uint32 as int32) == to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 1); };
  rewrite(to_integer((total as uint32 as int32 - remaining as uint32 as int32) - 1) == to_integer((total - remaining - 1u64) as uint32 as int32));
  normalize() using { to_integer(bytes[total - remaining - 1u64] as int32) == to_integer(bytes[(total - remaining - 1u64) as uint32 as int32] as int32); };
 }
}
