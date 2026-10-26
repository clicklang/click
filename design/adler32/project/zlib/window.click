import "block.click";
import click::integer;

// Mathematical observations of the original remaining count within one batch.
theorem zlib_remaining_step(total: uint64, remaining: uint64, amount: uint64) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires amount <= remaining;
 ensures to_integer(remaining - amount) <= to_integer(total) by solve() using { remaining <= total; total <= 5551u64; amount <= remaining; };
 ensures to_integer(total - (remaining - amount)) <= to_integer(5551u64) by solve() using { remaining <= total; total <= 5551u64; amount <= remaining; };
 ensures to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount) by {
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount); assumption();
 }
 ensures to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(amount) by {
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { remaining <= total; total <= 5551u64; };
  have to_integer(remaining - amount) <= to_integer(total) by solve() using { remaining <= total; total <= 5551u64; amount <= remaining; };
  have to_integer(total - (remaining - amount)) <= to_integer(22208u64) by solve() using { remaining <= total; total <= 5551u64; amount <= remaining; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_observation(total, remaining - amount));
  have to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
  have to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount);
  have to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount);
  solve() using {
   to_integer(zlib_prefix_count(total, remaining - amount)) == to_integer(total - (remaining - amount));
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(total - (remaining - amount)) == to_integer(total) - to_integer(remaining - amount);
   to_integer(total - remaining) == to_integer(total) - to_integer(remaining);
   to_integer(remaining - amount) == to_integer(remaining) - to_integer(amount);
  };
 }
}

// The lane index is a defined sum, stated apart so the observations of the
// sum in `zlib_block_lane` are stated where its definedness is established.
theorem zlib_block_lane_defined(bytes: uint8[], total: uint64, remaining: uint64, lane: int32) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires 16u64 <= remaining;
 requires 0 <= lane;
 requires lane <= 15;
 ensures defined(zlib_prefix_count(total, remaining) + lane) by {
  have to_integer(total - remaining) <= to_integer(5535u64) by solve() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; };
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { to_integer(total - remaining) <= to_integer(5535u64); };
  apply(zlib_prefix_observation(total, remaining));
  solve();
 }
}

theorem zlib_block_lane(bytes: uint8[], total: uint64, remaining: uint64, lane: int32) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires 16u64 <= remaining;
 requires 0 <= lane;
 requires lane <= 15;
 requires defined(zlib_prefix_count(total, remaining) + lane);
 ensures 0 <= to_integer(zlib_prefix_count(total, remaining) + lane) and to_integer(zlib_prefix_count(total, remaining) + lane) < 5552 by {
  have to_integer(total - remaining) <= to_integer(5535u64) by solve() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; };
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { to_integer(total - remaining) <= to_integer(5535u64); };
  apply(zlib_prefix_observation(total, remaining));
  have 0 <= to_integer(total - remaining); have to_integer(total - remaining) <= 18446744073709551615;
  have to_integer(zlib_prefix_count(total, remaining) + lane) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(lane);
  have 0 <= to_integer(zlib_prefix_count(total, remaining) + lane) by solve() using {
   to_integer(zlib_prefix_count(total, remaining) + lane) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(lane);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   0 <= to_integer(lane);
   0 <= to_integer(total - remaining);
  };
  have to_integer(zlib_prefix_count(total, remaining) + lane) <= 5550 by solve() using {
   to_integer(zlib_prefix_count(total, remaining) + lane) == to_integer(zlib_prefix_count(total, remaining)) + to_integer(lane);
   to_integer(zlib_prefix_count(total, remaining)) == to_integer(total - remaining);
   to_integer(total - remaining) <= 5535;
   to_integer(lane) <= 15;
  };
  both { assumption(); }
  and { solve() using { to_integer(zlib_prefix_count(total, remaining) + lane) <= 5550; }; }
 }
 ensures (bytes + (total - remaining))[lane] == bytes[zlib_prefix_count(total, remaining) + lane] by {
  have to_integer(total - remaining) <= to_integer(22208u64) by solve() using { remaining <= total; total <= 5551u64; };
  apply(zlib_prefix_observation(total, remaining));
  apply(zlib_prefix_pointer(bytes, total, remaining));
  have bytes + (total - remaining) + lane == bytes + (zlib_prefix_count(total, remaining) + lane) by {
   rewrite(bytes + (total - remaining) == bytes + zlib_prefix_count(total, remaining));
   normalize() using { defined(zlib_prefix_count(total, remaining) + lane); };
  }
  solve() using { bytes + (total - remaining) + lane == bytes + (zlib_prefix_count(total, remaining) + lane); };
 }
}

theorem zlib_block_read_bound(total: uint64, remaining: uint64, lane: uint64) {
 requires remaining <= total;
 requires total <= 5551u64;
 requires 16u64 <= remaining;
 requires lane <= 15u64;
 ensures to_integer(total - remaining) <= to_integer(5535u64) by solve() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; };
 ensures to_integer(total - remaining + lane) < to_integer(total) by solve() using { remaining <= total; total <= 5551u64; 16u64 <= remaining; lane <= 15u64; };
}
