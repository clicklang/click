import click::integer;

// Checked signed observations of native counts within the explicit signed limit.
// Iterator state and slice metadata retain their full unsigned 64-bit width.
theorem adler_bounded_count(count: uint64) {
 requires count <= 2147483647u64;
 ensures to_integer(count as uint32 as int32) == to_integer(count) by {
  have to_integer(count) <= 18446744073709551615;
  solve() using { 0 <= to_integer(count); to_integer(count) <= 2147483647; };
 }
 ensures 0 <= count as uint32 as int32 by {
  have to_integer(count) <= 18446744073709551615;
  have to_integer(count as uint32 as int32) == to_integer(count) by {
   solve() using { 0 <= to_integer(count); to_integer(count) <= 2147483647; };
  }
  have 0 <= to_integer(count as uint32 as int32) by { rewrite(to_integer(count as uint32 as int32), to_integer(count)); known(); }
  known();
 }
 ensures count as uint32 as int32 as uint64 == count by {
  have to_integer(count) <= 18446744073709551615;
  have to_integer(count as uint32 as int32) == to_integer(count) by {
   solve() using { 0 <= to_integer(count); to_integer(count) <= 2147483647; };
  }
  have 0 <= to_integer(count as uint32 as int32) by { rewrite(to_integer(count as uint32 as int32), to_integer(count)); known(); }
  have to_integer(count as uint32 as int32) <= 2147483647 by { rewrite(to_integer(count as uint32 as int32), to_integer(count)); known(); }
  have to_integer(count as uint32 as int32 as uint64) == to_integer(count as uint32 as int32) by {
   solve() using { 0 <= to_integer(count as uint32 as int32); to_integer(count as uint32 as int32) <= 2147483647; };
  }
  have to_integer(count as uint32 as int32 as uint64) == to_integer(count) by { rewrite(to_integer(count as uint32 as int32 as uint64), to_integer(count as uint32 as int32)); known(); }
  known();
 }
}


theorem adler_bounded_pointer_index(base: const uint8*, count: uint64) {
 requires count <= 2147483647u64;
 ensures base + count == base + count as uint32 as int32 by {
  apply(adler_bounded_count(count));
  solve() using { to_integer(count as uint32 as int32) == to_integer(count); count as uint32 as int32 as uint64 == count; 0 <= count as uint32 as int32; count <= 2147483647u64; };
 }
}

theorem adler_bounded_count_lower(count: uint64, low: int32) {
 requires count <= 2147483647u64;
 requires 0 <= low;
 requires low as uint64 <= count;
 ensures low <= count as uint32 as int32 by {
  apply(adler_bounded_count(count));
  have low <= 2147483647 by normalize();
  have to_integer(low as uint64) == to_integer(low) by {
   solve() using { 0 <= to_integer(low); to_integer(low) <= 2147483647; };
  }
  have to_integer(low) <= to_integer(count as uint32 as int32) by {
   rewrite(to_integer(count as uint32 as int32), to_integer(count));
   rewrite(to_integer(low), to_integer(low as uint64));
   known();
  }
  known();
 }
}

theorem adler_bounded_count_upper(count: uint64, high: int32) {
 requires count <= 2147483647u64;
 requires 0 <= high;
 requires count <= high as uint64;
 ensures count as uint32 as int32 <= high by {
  apply(adler_bounded_count(count));
  have high <= 2147483647 by normalize();
  have to_integer(high as uint64) == to_integer(high) by {
   solve() using { 0 <= to_integer(high); to_integer(high) <= 2147483647; };
  }
  have to_integer(count as uint32 as int32) <= to_integer(high) by {
   rewrite(to_integer(count as uint32 as int32), to_integer(count));
   rewrite(to_integer(high), to_integer(high as uint64));
   known();
  }
  known();
 }
}
