import click::integer;

// Checked positions in the aligned remainder after any number of full batches.

theorem adler_empty_remainder_position(total: int32, remaining: int32) {
 requires 0 <= total;
 requires remaining == total;
 ensures to_integer(total - remaining) == 0 by {
  have 0 <= remaining by { rewrite(remaining == total); assumption(); }
  have remaining <= total by { rewrite(remaining == total); normalize(); }
  have to_integer(remaining) == to_integer(total) by { rewrite(remaining == total); normalize(); }
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  solve() using { to_integer(total - remaining) == to_integer(total) - to_integer(remaining); to_integer(remaining) == to_integer(total); };
 }
}

theorem adler_complete_remainder_position(total: int32, remaining: int32) {
 requires 0 <= total;
 requires remaining == 0;
 ensures to_integer(total - remaining) == to_integer(total) by {
  have 0 <= remaining by { rewrite(remaining == 0); normalize(); }
  have remaining <= total by { rewrite(remaining == 0); assumption(); }
  have to_integer(remaining) == 0 by { rewrite(remaining == 0); normalize(); }
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  solve() using { to_integer(total - remaining) == to_integer(total) - to_integer(remaining); to_integer(remaining) == 0; };
 }
}

// The native deferred product uses uint32; the prefix position uses int32.
theorem adler_remainder_native_count_observation(count: uint64) {
 requires count <= 22204u64;
 ensures to_integer(count as uint32) == to_integer(count) by {
  have to_integer(count) <= 18446744073709551615;
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(count) => 0 <= to_integer(count);
   premise 1: to_integer(count) <= 22204 => to_integer(count) <= 22204;
   integer_cast_identity bounds [0, 1] => to_integer(count as uint32) == to_integer(count);
   conclusion 0;
  }
 }
}
