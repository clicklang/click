import click::integer;

// Exact native B transitions for a deferred full-batch contribution.
// Assemble after the common specification, lane-state and vector-prefix.

theorem adler_native_deferred_b_step(pos: int32, a: uint32, b: uint32, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= pos;
 requires pos <= 22204;
 requires 0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))) == adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)) + 4 * adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)) + 4 * to_integer(v0) + 3 * to_integer(v1) + 2 * to_integer(v2) + to_integer(v3) by {
  have defined(pos + 4) by solve() using { 0 <= pos; pos <= 22204; };
  have to_integer(pos + 4) == to_integer(pos) + to_integer(4);
  have to_integer(a0 + v0) == to_integer(a0) + to_integer(v0);
  have to_integer(b0) + to_integer(a0 + v0) <= 4294967295 by { rewrite(to_integer(a0 + v0), to_integer(a0) + to_integer(v0)); known(); }
  have to_integer(b0 + (a0 + v0)) == to_integer(b0) + to_integer((a0 + v0));
  have to_integer(a1 + v1) == to_integer(a1) + to_integer(v1);
  have to_integer(b1) + to_integer(a1 + v1) <= 4294967295 by { rewrite(to_integer(a1 + v1), to_integer(a1) + to_integer(v1)); known(); }
  have to_integer(b1 + (a1 + v1)) == to_integer(b1) + to_integer((a1 + v1));
  have to_integer(a2 + v2) == to_integer(a2) + to_integer(v2);
  have to_integer(b2) + to_integer(a2 + v2) <= 4294967295 by { rewrite(to_integer(a2 + v2), to_integer(a2) + to_integer(v2)); known(); }
  have to_integer(b2 + (a2 + v2)) == to_integer(b2) + to_integer((a2 + v2));
  have to_integer(a3 + v3) == to_integer(a3) + to_integer(v3);
  have to_integer(b3) + to_integer(a3 + v3) <= 4294967295 by { rewrite(to_integer(a3 + v3), to_integer(a3) + to_integer(v3)); known(); }
  have to_integer(b3 + (a3 + v3)) == to_integer(b3) + to_integer((a3 + v3));
  apply(adler_four_lane_state_step(to_integer(a), to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3), to_integer(v0), to_integer(v1), to_integer(v2), to_integer(v3)));
  rewrite(to_integer(a1 + v1), to_integer(a1) + to_integer(v1));
  rewrite(to_integer(a2 + v2), to_integer(a2) + to_integer(v2));
  rewrite(to_integer(a3 + v3), to_integer(a3) + to_integer(v3));
  rewrite(to_integer(b0 + (a0 + v0)), to_integer(b0) + to_integer(a0 + v0));
  rewrite(to_integer(a0 + v0), to_integer(a0) + to_integer(v0));
  rewrite(to_integer(b1 + (a1 + v1)), to_integer(b1) + to_integer(a1 + v1));
  rewrite(to_integer(a1 + v1), to_integer(a1) + to_integer(v1));
  rewrite(to_integer(b2 + (a2 + v2)), to_integer(b2) + to_integer(a2 + v2));
  rewrite(to_integer(a2 + v2), to_integer(a2) + to_integer(v2));
  rewrite(to_integer(b3 + (a3 + v3)), to_integer(b3) + to_integer(a3 + v3));
  rewrite(to_integer(a3 + v3), to_integer(a3) + to_integer(v3));
  rewrite(to_integer(pos + 4), to_integer(pos) + to_integer(4));
  have to_integer(b) + (to_integer(pos) + 4) * to_integer(a) == (to_integer(b) + to_integer(pos) * to_integer(a)) + 4 * to_integer(a) by { solve() using {  }; }
  rewrite(to_integer(b) + (to_integer(pos) + 4) * to_integer(a), (to_integer(b) + to_integer(pos) * to_integer(a)) + 4 * to_integer(a));
  have to_integer(b0) + (to_integer(a0) + to_integer(v0)) == to_integer(b0) + to_integer(a0) + to_integer(v0) by solve() using {};
  rewrite(to_integer(b0) + (to_integer(a0) + to_integer(v0)), to_integer(b0) + to_integer(a0) + to_integer(v0));
  have to_integer(b1) + (to_integer(a1) + to_integer(v1)) == to_integer(b1) + to_integer(a1) + to_integer(v1) by solve() using {};
  rewrite(to_integer(b1) + (to_integer(a1) + to_integer(v1)), to_integer(b1) + to_integer(a1) + to_integer(v1));
  have to_integer(b2) + (to_integer(a2) + to_integer(v2)) == to_integer(b2) + to_integer(a2) + to_integer(v2) by solve() using {};
  rewrite(to_integer(b2) + (to_integer(a2) + to_integer(v2)), to_integer(b2) + to_integer(a2) + to_integer(v2));
  have to_integer(b3) + (to_integer(a3) + to_integer(v3)) == to_integer(b3) + to_integer(a3) + to_integer(v3) by solve() using {};
  rewrite(to_integer(b3) + (to_integer(a3) + to_integer(v3)), to_integer(b3) + to_integer(a3) + to_integer(v3));
  known();
 }
}

theorem adler_nonnegative_deferred_b_step(pos: int32, a: uint32, b: uint32, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= pos;
 requires pos <= 22204;
 requires 0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures 0 <= adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))) by {
  apply(adler_native_deferred_b_step(pos, a, b, a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3));
  have 0 <= to_integer(a);
  have 0 <= to_integer(a0);
  have 0 <= to_integer(a1);
  have 0 <= to_integer(a2);
  have 0 <= to_integer(a3);
  have 0 <= to_integer(v0);
  have 0 <= to_integer(v1);
  have 0 <= to_integer(v2);
  have 0 <= to_integer(v3);
  have 0 <= adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)) by { unfold(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3))); solve() using { 0 <= to_integer(a); 0 <= to_integer(a0); 0 <= to_integer(a1); 0 <= to_integer(a2); 0 <= to_integer(a3); }; }
  rewrite(adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))), adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)) + 4 * adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)) + 4 * to_integer(v0) + 3 * to_integer(v1) + 2 * to_integer(v2) + to_integer(v3));
  solve() using { 0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)); 0 <= adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)); 0 <= to_integer(v0); 0 <= to_integer(v1); 0 <= to_integer(v2); 0 <= to_integer(v3); };
 }
}

theorem adler_canonical_lane_b_floor(b: Integer, a1: Integer, a2: Integer, a3: Integer, b0: Integer, b1: Integer, b2: Integer, b3: Integer) {
 requires 0 <= b;
 requires a1 <= 65520;
 requires a2 <= 65520;
 requires a3 <= 65520;
 requires 0 <= b0;
 requires 0 <= b1;
 requires 0 <= b2;
 requires 0 <= b3;
 ensures 0 <= adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3) by {
  have 0 <= b + 4 * (b0 + b1 + b2 + b3) by {
   solve() using { 0 <= b; 0 <= b0; 0 <= b1; 0 <= b2; 0 <= b3; };
  }
  have a1 + 2 * a2 + 3 * a3 <= 393120 by {
   solve() using { a1 <= 65520; a2 <= 65520; a3 <= 65520; };
  }
  unfold(adler_lane_b(b, a1, a2, a3, b0, b1, b2, b3));
  solve() using { 0 <= b + 4 * (b0 + b1 + b2 + b3); a1 + 2 * a2 + 3 * a3 <= 393120; };
 }
}

// Observe the checked native position as a whole, after its iterator endpoint
// is established. This also retains the int32 subtraction guard explicitly.
theorem adler_empty_full_batch_position(remaining: int32) {
 requires remaining == 22208;
 ensures to_integer(22208 - remaining) == 0 by {
  rewrite(remaining, 22208);
  known();
 }
}

theorem adler_complete_full_batch_position(remaining: int32) {
 requires remaining == 0;
 ensures to_integer(22208 - remaining) == 22208 by {
  rewrite(remaining, 0);
  known();
 }
}

// Couple the batch-local deferred state to the original input global prefix.
theorem adler_native_deferred_b_prefix_step(bytes: uint8[], n: int32, pos: int32, a_seed: Integer, b_seed: Integer, a: uint32, b: uint32, a0: uint32, a1: uint32, a2: uint32, a3: uint32, b0: uint32, b1: uint32, b2: uint32, b3: uint32, v0: uint32, v1: uint32, v2: uint32, v3: uint32) {
 requires 0 <= n;
 requires n <= 2147483643;
 requires 0 <= pos;
 requires pos <= 22204;
 requires 0 <= a_seed;
 requires a_seed <= 65520;
 requires 0 <= b_seed;
 requires 0 <= adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3));
 requires truncating_remainder(adler_lane_a(to_integer(a), to_integer(a0), to_integer(a1), to_integer(a2), to_integer(a3)), 65521) == adler_spec_a(bytes, n, a_seed);
 requires truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos) * to_integer(a), to_integer(a1), to_integer(a2), to_integer(a3), to_integer(b0), to_integer(b1), to_integer(b2), to_integer(b3)), 65521) == adler_spec_b(bytes, n, a_seed, b_seed);
 requires to_integer(v0) == to_integer(bytes[n] as int32);
 requires to_integer(a0) + to_integer(v0) <= 4294967295;
 requires to_integer(b0) + (to_integer(a0) + to_integer(v0)) <= 4294967295;
 requires to_integer(v1) == to_integer(bytes[n + 1] as int32);
 requires to_integer(a1) + to_integer(v1) <= 4294967295;
 requires to_integer(b1) + (to_integer(a1) + to_integer(v1)) <= 4294967295;
 requires to_integer(v2) == to_integer(bytes[n + 2] as int32);
 requires to_integer(a2) + to_integer(v2) <= 4294967295;
 requires to_integer(b2) + (to_integer(a2) + to_integer(v2)) <= 4294967295;
 requires to_integer(v3) == to_integer(bytes[n + 3] as int32);
 requires to_integer(a3) + to_integer(v3) <= 4294967295;
 requires to_integer(b3) + (to_integer(a3) + to_integer(v3)) <= 4294967295;
 ensures truncating_remainder(adler_lane_b(to_integer(b) + to_integer(pos + 4) * to_integer(a), to_integer(a1 + v1), to_integer(a2 + v2), to_integer(a3 + v3), to_integer(b0 + (a0 + v0)), to_integer(b1 + (a1 + v1)), to_integer(b2 + (a2 + v2)), to_integer(b3 + (a3 + v3))), 65521) == adler_spec_b(bytes, n + 4, a_seed, b_seed) by {
  have defined(n + 1) by solve() using { 0 <= n; n <= 2147483643; };
  have defined(n + 2) by solve() using { 0 <= n; n <= 2147483643; };
  have defined(n + 3) by solve() using { 0 <= n; n <= 2147483643; };
  have 0 <= to_integer(a) by known();
  apply(adler_native_four_lane_prefix_step(bytes, n, a_seed, b_seed, to_integer(a), to_integer(b) + to_integer(pos) * to_integer(a), a0, a1, a2, a3, b0, b1, b2, b3, v0, v1, v2, v3));
  have defined(pos + 4) by solve() using { 0 <= pos; pos <= 22204; };
  have to_integer(pos + 4) == to_integer(pos) + to_integer(4);
  rewrite(to_integer(pos + 4), to_integer(pos) + to_integer(4));
  have to_integer(b) + (to_integer(pos) + 4) * to_integer(a) == (to_integer(b) + to_integer(pos) * to_integer(a)) + 4 * to_integer(a) by {
   solve() using {  };
  }
  rewrite(to_integer(b) + (to_integer(pos) + 4) * to_integer(a), (to_integer(b) + to_integer(pos) * to_integer(a)) + 4 * to_integer(a));
  known();
 }
}

theorem adler_zero_lane_b_residue(b: Integer) {
 requires 0 <= b;
 requires b <= 65520;
 ensures truncating_remainder(adler_lane_b(b, 0, 0, 0, 0, 0, 0, 0), 65521) == b by {
  have 0 <= b + 393126 by solve() using { 0 <= b; };
  have b + 393126 == 6 * 65521 + b by solve() using {};
  apply(adler_residue_unique(b + 393126, 6, b));
  unfold(adler_lane_b(b, 0, 0, 0, 0, 0, 0, 0));
  have b + 4 * (0 + 0 + 0 + 0) + 393126 - 0 - 2 * 0 - 3 * 0 == b + 393126 by solve() using {};
  rewrite(b + 4 * (0 + 0 + 0 + 0) + 393126 - 0 - 2 * 0 - 3 * 0, b + 393126);
  known();
 }
}
