target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "batch-helpers.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len == 5552u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 5552u64, 1, 0);
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
 } by {
 have to_integer(5552) == to_integer(5552u64) by normalize();
 apply(adler_spec_checksum_bridge(buf, 5552, 5552u64, 1, 0)) using { to_integer(5552) == to_integer(5552u64); };
 have viewable(buf[0u64..len]) by solve();
 step_until(loop(1));
 loop {
  decreases to_integer(len);
  invariant len == 5552u64 or len == 0u64;
  invariant len <= 5552u64;
  invariant old(len) == 5552u64;
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant adler <= 65520u64;
  invariant sum2 <= 65520u64;
  invariant to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1);
  invariant to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0);
  initialize by {
   have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); solve(); }
   apply(zlib_batch_empty_components(old(buf)));
   have adler == 1u64 by solve();
   have sum2 == 0u64 by solve();
   have to_integer(adler) == 1 by solve() using { adler == 1u64; };
   have to_integer(sum2) == 0 by solve() using { sum2 == 0u64; };
   have adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by solve() using {
    to_integer(adler) == 1;
    adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1;
   };
   have to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by solve() using {
    to_integer(sum2) == 0;
    adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0;
   };
   solve();
  }
  preserve by {
   have 5552u64 <= len by assumption();
   have len == 5552u64 by solve() using { 5552u64 <= len; len <= 5552u64; };
   have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); solve(); }
   apply(zlib_batch_empty_components(old(buf)));
   have adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0 by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(adler) == 1 by solve() using {
    to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1);
    adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) == 1;
   };
   have to_integer(sum2) == 0 by solve() using {
    to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0);
    adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) == 0;
   };
   have viewable(buf[0u64..5552u64]) by solve();
   mark batch_entry;
   step(); step();
   step_until(loop(2));
   loop {
    decreases to_integer(n);
    invariant 1u32 <= n;
    invariant n <= 347u32;
    invariant len == 0u64;
    invariant old(len) == 5552u64;
    invariant buf == old(buf) + zlib_batch_count(n);
    invariant viewable(buf[0u64..16u64 * n as uint64]);
    invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n));
    invariant to_integer(sum2) == to_integer(zlib_batch_count(n)) + adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n));
    invariant to_integer(adler) <= 1 + 255 * to_integer(zlib_batch_count(n));
    invariant to_integer(sum2) <= 1415761 * to_integer(zlib_batch_count(n));
    initialize by {
     have n == 347u32 by solve();
     have len == 0u64 by solve();
     have buf == old(buf) by solve();
     have to_integer(adler) == 1 by assumption();
     have to_integer(sum2) == 0 by assumption();
     have viewable(buf[0u64..5552u64]) by {
      transport(at(batch_entry, viewable(buf[0u64..5552u64])), viewable(buf[0u64..5552u64])) using {
       at(batch_entry, viewable(buf[0u64..5552u64]));
      };
     }
     have viewable(buf[0u64..16u64 * n as uint64]) by assumption();
     apply(zlib_batch_prefix_initial());
     have zlib_batch_count(n) == 0 by assumption();
     apply(adler_sum_empty(old(buf), 0));
     have buf == old(buf) + zlib_batch_count(n) by { rewrite(zlib_batch_count(n) == 0); assumption(); }
     have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n) == 0); rewrite(adler_byte_sum(old(buf), 0) == 0); assumption();
     }
     have to_integer(sum2) == to_integer(zlib_batch_count(n)) + adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n) == 0); rewrite(adler_weighted_sum(old(buf), 0, 0) == 0); assumption();
     }
     have to_integer(adler) <= 1 + 255 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n) == 0); solve() using { to_integer(adler) == 1; }; }
     have to_integer(sum2) <= 1415761 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n) == 0); solve() using { to_integer(sum2) == 0; }; }
     solve();
    }
    preserve by {
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     apply(zlib_batch_remaining_limit(n));
     apply(zlib_batch_nonempty_remaining(n));
     have 16u64 <= 16u64 * n as uint64 by { unfold(zlib_batch_remaining(n)); assumption(); }
     have 16u64 * n as uint64 <= 5552u64 by { unfold(zlib_batch_remaining(n)); assumption(); }
     have 1u64 <= 16u64 * n as uint64 by solve() using { 16u64 <= 16u64 * n as uint64; };
     have 16u64 * n as uint64 <= 9223372036854775807u64 by solve() using { 16u64 * n as uint64 <= 5552u64; };
     apply(zlib_batch_cursor(old(buf), n));
     have buf == old(buf) + (5552u64 - zlib_batch_remaining(n)) by solve() using {
      buf == old(buf) + zlib_batch_count(n);
      old(buf) + zlib_batch_count(n) == old(buf) + (5552u64 - zlib_batch_remaining(n));
     };
     have 5552u64 - zlib_batch_remaining(n) < 5552u64 by solve() using { 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
     have 5552u64 - zlib_batch_remaining(n) < old(len) by solve() using { 5552u64 - zlib_batch_remaining(n) < 5552u64; old(len) == 5552u64; };
     have old(len) <= 9223372036854775807u64 by solve() using { old(len) == 5552u64; };

     mark before_block;
   step_until(assignment(adler, 5));
   apply(zlib_batch_read_bound(n, 0u64));
   apply(zlib_batch_lane_defined(n, 0)); apply(zlib_batch_lane(n, 0));
   apply(zlib_batch_byte_lane(old(buf), n, 0));
   have buf[0] == old(buf)[zlib_batch_count(n)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[0] == old(buf)[zlib_batch_count(n) + 0];
   };
   apply(zlib_native_component_step(old(buf), zlib_batch_count(n), adler, sum2, buf[0]));
   have viewable(buf[0u64..1u64]) by solve();
   mark byte_0;
   step();
   step_until(assignment(sum2, 5));
   step();
   have adler == at(byte_0, adler + buf[0] as uint32 as uint64) by solve();
   have sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n) + 1) by solve() using {
    adler == at(byte_0, adler + buf[0] as uint32 as uint64);
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) == to_integer(zlib_batch_count(n) + 1) + adler_weighted_sum(old(buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1) by solve() using {
    sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) == to_integer(zlib_batch_count(n) + 1) + adler_weighted_sum(old(buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_batch_count(n) + 1) by solve() using {
    adler == at(byte_0, adler + buf[0] as uint32 as uint64);
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) <= 1 + 255 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer(zlib_batch_count(n) + 1) by solve() using {
    sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) <= 1415761 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 1)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 1)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 1), (zlib_batch_count(n) + 1)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 1)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 1)) by solve();
   step_until(assignment(adler, 6));
   apply(zlib_batch_read_bound(n, 1u64));
   apply(zlib_batch_lane_defined(n, 1)); apply(zlib_batch_lane(n, 1));
   apply(zlib_batch_byte_lane(old(buf), n, 1));
   have buf[1] == old(buf)[(zlib_batch_count(n) + 1)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[1] == old(buf)[zlib_batch_count(n) + 1];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 1), adler, sum2, buf[1]));
   mark byte_1;
   step();
   step_until(assignment(sum2, 6));
   step();
   have adler == at(byte_1, adler + buf[1] as uint32 as uint64) by solve();
   have sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 1) + 1) by solve() using {
    adler == at(byte_1, adler + buf[1] as uint32 as uint64);
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1) by solve() using {
    sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 1) + 1) by solve() using {
    adler == at(byte_1, adler + buf[1] as uint32 as uint64);
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 1) + 1) by solve() using {
    sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 2)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 2)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 2), (zlib_batch_count(n) + 2)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 2)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 2)) by solve();
   step_until(assignment(adler, 7));
   apply(zlib_batch_read_bound(n, 2u64));
   apply(zlib_batch_lane_defined(n, 2)); apply(zlib_batch_lane(n, 2));
   apply(zlib_batch_byte_lane(old(buf), n, 2));
   have buf[2] == old(buf)[(zlib_batch_count(n) + 2)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[2] == old(buf)[zlib_batch_count(n) + 2];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 2), adler, sum2, buf[2]));
   mark byte_2;
   step();
   step_until(assignment(sum2, 7));
   step();
   have adler == at(byte_2, adler + buf[2] as uint32 as uint64) by solve();
   have sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 2) + 1) by solve() using {
    adler == at(byte_2, adler + buf[2] as uint32 as uint64);
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1) by solve() using {
    sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 2) + 1) by solve() using {
    adler == at(byte_2, adler + buf[2] as uint32 as uint64);
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 2) + 1) by solve() using {
    sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 3)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 3)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 3), (zlib_batch_count(n) + 3)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 3)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 3)) by solve();
   step_until(assignment(adler, 8));
   apply(zlib_batch_read_bound(n, 3u64));
   apply(zlib_batch_lane_defined(n, 3)); apply(zlib_batch_lane(n, 3));
   apply(zlib_batch_byte_lane(old(buf), n, 3));
   have buf[3] == old(buf)[(zlib_batch_count(n) + 3)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[3] == old(buf)[zlib_batch_count(n) + 3];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 3), adler, sum2, buf[3]));
   mark byte_3;
   step();
   step_until(assignment(sum2, 8));
   step();
   have adler == at(byte_3, adler + buf[3] as uint32 as uint64) by solve();
   have sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 3) + 1) by solve() using {
    adler == at(byte_3, adler + buf[3] as uint32 as uint64);
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1) by solve() using {
    sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 3) + 1) by solve() using {
    adler == at(byte_3, adler + buf[3] as uint32 as uint64);
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 3) + 1) by solve() using {
    sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 4)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 4)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 4), (zlib_batch_count(n) + 4)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 4)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 4)) by solve();
   step_until(assignment(adler, 9));
   apply(zlib_batch_read_bound(n, 4u64));
   apply(zlib_batch_lane_defined(n, 4)); apply(zlib_batch_lane(n, 4));
   apply(zlib_batch_byte_lane(old(buf), n, 4));
   have buf[4] == old(buf)[(zlib_batch_count(n) + 4)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[4] == old(buf)[zlib_batch_count(n) + 4];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 4), adler, sum2, buf[4]));
   mark byte_4;
   step();
   step_until(assignment(sum2, 9));
   step();
   have adler == at(byte_4, adler + buf[4] as uint32 as uint64) by solve();
   have sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 4) + 1) by solve() using {
    adler == at(byte_4, adler + buf[4] as uint32 as uint64);
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1) by solve() using {
    sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 4) + 1) by solve() using {
    adler == at(byte_4, adler + buf[4] as uint32 as uint64);
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 4) + 1) by solve() using {
    sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 5)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 5)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 5), (zlib_batch_count(n) + 5)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 5)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 5)) by solve();
   step_until(assignment(adler, 10));
   apply(zlib_batch_read_bound(n, 5u64));
   apply(zlib_batch_lane_defined(n, 5)); apply(zlib_batch_lane(n, 5));
   apply(zlib_batch_byte_lane(old(buf), n, 5));
   have buf[5] == old(buf)[(zlib_batch_count(n) + 5)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[5] == old(buf)[zlib_batch_count(n) + 5];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 5), adler, sum2, buf[5]));
   mark byte_5;
   step();
   step_until(assignment(sum2, 10));
   step();
   have adler == at(byte_5, adler + buf[5] as uint32 as uint64) by solve();
   have sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 5) + 1) by solve() using {
    adler == at(byte_5, adler + buf[5] as uint32 as uint64);
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1) by solve() using {
    sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 5) + 1) by solve() using {
    adler == at(byte_5, adler + buf[5] as uint32 as uint64);
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 5) + 1) by solve() using {
    sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 6)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 6)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 6), (zlib_batch_count(n) + 6)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 6)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 6)) by solve();
   step_until(assignment(adler, 11));
   apply(zlib_batch_read_bound(n, 6u64));
   apply(zlib_batch_lane_defined(n, 6)); apply(zlib_batch_lane(n, 6));
   apply(zlib_batch_byte_lane(old(buf), n, 6));
   have buf[6] == old(buf)[(zlib_batch_count(n) + 6)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[6] == old(buf)[zlib_batch_count(n) + 6];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 6), adler, sum2, buf[6]));
   mark byte_6;
   step();
   step_until(assignment(sum2, 11));
   step();
   have adler == at(byte_6, adler + buf[6] as uint32 as uint64) by solve();
   have sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 6) + 1) by solve() using {
    adler == at(byte_6, adler + buf[6] as uint32 as uint64);
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1) by solve() using {
    sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 6) + 1) by solve() using {
    adler == at(byte_6, adler + buf[6] as uint32 as uint64);
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 6) + 1) by solve() using {
    sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 7)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 7)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 7), (zlib_batch_count(n) + 7)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 7)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 7)) by solve();
   step_until(assignment(adler, 12));
   apply(zlib_batch_read_bound(n, 7u64));
   apply(zlib_batch_lane_defined(n, 7)); apply(zlib_batch_lane(n, 7));
   apply(zlib_batch_byte_lane(old(buf), n, 7));
   have buf[7] == old(buf)[(zlib_batch_count(n) + 7)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[7] == old(buf)[zlib_batch_count(n) + 7];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 7), adler, sum2, buf[7]));
   mark byte_7;
   step();
   step_until(assignment(sum2, 12));
   step();
   have adler == at(byte_7, adler + buf[7] as uint32 as uint64) by solve();
   have sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 7) + 1) by solve() using {
    adler == at(byte_7, adler + buf[7] as uint32 as uint64);
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1) by solve() using {
    sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 7) + 1) by solve() using {
    adler == at(byte_7, adler + buf[7] as uint32 as uint64);
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 7) + 1) by solve() using {
    sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 8)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 8)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 8), (zlib_batch_count(n) + 8)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 8)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 8)) by solve();
   step_until(assignment(adler, 13));
   apply(zlib_batch_read_bound(n, 8u64));
   apply(zlib_batch_lane_defined(n, 8)); apply(zlib_batch_lane(n, 8));
   apply(zlib_batch_byte_lane(old(buf), n, 8));
   have buf[8] == old(buf)[(zlib_batch_count(n) + 8)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[8] == old(buf)[zlib_batch_count(n) + 8];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 8), adler, sum2, buf[8]));
   mark byte_8;
   step();
   step_until(assignment(sum2, 13));
   step();
   have adler == at(byte_8, adler + buf[8] as uint32 as uint64) by solve();
   have sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 8) + 1) by solve() using {
    adler == at(byte_8, adler + buf[8] as uint32 as uint64);
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1) by solve() using {
    sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 8) + 1) by solve() using {
    adler == at(byte_8, adler + buf[8] as uint32 as uint64);
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 8) + 1) by solve() using {
    sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 9)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 9)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 9), (zlib_batch_count(n) + 9)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 9)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 9)) by solve();
   step_until(assignment(adler, 14));
   apply(zlib_batch_read_bound(n, 9u64));
   apply(zlib_batch_lane_defined(n, 9)); apply(zlib_batch_lane(n, 9));
   apply(zlib_batch_byte_lane(old(buf), n, 9));
   have buf[9] == old(buf)[(zlib_batch_count(n) + 9)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[9] == old(buf)[zlib_batch_count(n) + 9];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 9), adler, sum2, buf[9]));
   mark byte_9;
   step();
   step_until(assignment(sum2, 14));
   step();
   have adler == at(byte_9, adler + buf[9] as uint32 as uint64) by solve();
   have sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 9) + 1) by solve() using {
    adler == at(byte_9, adler + buf[9] as uint32 as uint64);
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1) by solve() using {
    sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 9) + 1) by solve() using {
    adler == at(byte_9, adler + buf[9] as uint32 as uint64);
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 9) + 1) by solve() using {
    sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 10)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 10)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 10), (zlib_batch_count(n) + 10)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 10)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 10)) by solve();
   step_until(assignment(adler, 15));
   apply(zlib_batch_read_bound(n, 10u64));
   apply(zlib_batch_lane_defined(n, 10)); apply(zlib_batch_lane(n, 10));
   apply(zlib_batch_byte_lane(old(buf), n, 10));
   have buf[10] == old(buf)[(zlib_batch_count(n) + 10)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[10] == old(buf)[zlib_batch_count(n) + 10];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 10), adler, sum2, buf[10]));
   mark byte_10;
   step();
   step_until(assignment(sum2, 15));
   step();
   have adler == at(byte_10, adler + buf[10] as uint32 as uint64) by solve();
   have sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 10) + 1) by solve() using {
    adler == at(byte_10, adler + buf[10] as uint32 as uint64);
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1) by solve() using {
    sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 10) + 1) by solve() using {
    adler == at(byte_10, adler + buf[10] as uint32 as uint64);
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 10) + 1) by solve() using {
    sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 11)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 11)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 11), (zlib_batch_count(n) + 11)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 11)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 11)) by solve();
   step_until(assignment(adler, 16));
   apply(zlib_batch_read_bound(n, 11u64));
   apply(zlib_batch_lane_defined(n, 11)); apply(zlib_batch_lane(n, 11));
   apply(zlib_batch_byte_lane(old(buf), n, 11));
   have buf[11] == old(buf)[(zlib_batch_count(n) + 11)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[11] == old(buf)[zlib_batch_count(n) + 11];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 11), adler, sum2, buf[11]));
   mark byte_11;
   step();
   step_until(assignment(sum2, 16));
   step();
   have adler == at(byte_11, adler + buf[11] as uint32 as uint64) by solve();
   have sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 11) + 1) by solve() using {
    adler == at(byte_11, adler + buf[11] as uint32 as uint64);
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1) by solve() using {
    sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 11) + 1) by solve() using {
    adler == at(byte_11, adler + buf[11] as uint32 as uint64);
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 11) + 1) by solve() using {
    sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 12)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 12)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 12), (zlib_batch_count(n) + 12)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 12)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 12)) by solve();
   step_until(assignment(adler, 17));
   apply(zlib_batch_read_bound(n, 12u64));
   apply(zlib_batch_lane_defined(n, 12)); apply(zlib_batch_lane(n, 12));
   apply(zlib_batch_byte_lane(old(buf), n, 12));
   have buf[12] == old(buf)[(zlib_batch_count(n) + 12)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[12] == old(buf)[zlib_batch_count(n) + 12];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 12), adler, sum2, buf[12]));
   mark byte_12;
   step();
   step_until(assignment(sum2, 17));
   step();
   have adler == at(byte_12, adler + buf[12] as uint32 as uint64) by solve();
   have sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 12) + 1) by solve() using {
    adler == at(byte_12, adler + buf[12] as uint32 as uint64);
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1) by solve() using {
    sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 12) + 1) by solve() using {
    adler == at(byte_12, adler + buf[12] as uint32 as uint64);
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 12) + 1) by solve() using {
    sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 13)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 13)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 13), (zlib_batch_count(n) + 13)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 13)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 13)) by solve();
   step_until(assignment(adler, 18));
   apply(zlib_batch_read_bound(n, 13u64));
   apply(zlib_batch_lane_defined(n, 13)); apply(zlib_batch_lane(n, 13));
   apply(zlib_batch_byte_lane(old(buf), n, 13));
   have buf[13] == old(buf)[(zlib_batch_count(n) + 13)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[13] == old(buf)[zlib_batch_count(n) + 13];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 13), adler, sum2, buf[13]));
   mark byte_13;
   step();
   step_until(assignment(sum2, 18));
   step();
   have adler == at(byte_13, adler + buf[13] as uint32 as uint64) by solve();
   have sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 13) + 1) by solve() using {
    adler == at(byte_13, adler + buf[13] as uint32 as uint64);
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1) by solve() using {
    sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 13) + 1) by solve() using {
    adler == at(byte_13, adler + buf[13] as uint32 as uint64);
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 13) + 1) by solve() using {
    sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 14)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 14)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 14), (zlib_batch_count(n) + 14)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 14)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 14)) by solve();
   step_until(assignment(adler, 19));
   apply(zlib_batch_read_bound(n, 14u64));
   apply(zlib_batch_lane_defined(n, 14)); apply(zlib_batch_lane(n, 14));
   apply(zlib_batch_byte_lane(old(buf), n, 14));
   have buf[14] == old(buf)[(zlib_batch_count(n) + 14)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[14] == old(buf)[zlib_batch_count(n) + 14];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 14), adler, sum2, buf[14]));
   mark byte_14;
   step();
   step_until(assignment(sum2, 19));
   step();
   have adler == at(byte_14, adler + buf[14] as uint32 as uint64) by solve();
   have sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 14) + 1) by solve() using {
    adler == at(byte_14, adler + buf[14] as uint32 as uint64);
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1) by solve() using {
    sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 14) + 1) by solve() using {
    adler == at(byte_14, adler + buf[14] as uint32 as uint64);
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 14) + 1) by solve() using {
    sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 15)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 15)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 15), (zlib_batch_count(n) + 15)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 15)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 15)) by solve();
   step_until(assignment(adler, 20));
   apply(zlib_batch_read_bound(n, 15u64));
   apply(zlib_batch_lane_defined(n, 15)); apply(zlib_batch_lane(n, 15));
   apply(zlib_batch_byte_lane(old(buf), n, 15));
   have buf[15] == old(buf)[(zlib_batch_count(n) + 15)] by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    (old(buf) + zlib_batch_count(n))[15] == old(buf)[zlib_batch_count(n) + 15];
   };
   apply(zlib_native_component_step(old(buf), (zlib_batch_count(n) + 15), adler, sum2, buf[15]));
   mark byte_15;
   step();
   step_until(assignment(sum2, 20));
   step();
   have adler == at(byte_15, adler + buf[15] as uint32 as uint64) by solve();
   have sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 15) + 1) by solve() using {
    adler == at(byte_15, adler + buf[15] as uint32 as uint64);
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1) by solve() using {
    sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) == to_integer((zlib_batch_count(n) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 15) + 1) by solve() using {
    adler == at(byte_15, adler + buf[15] as uint32 as uint64);
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 15) + 1) by solve() using {
    sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) <= 1415761 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_batch_count(n) + 16)) by solve();
   have to_integer(sum2) == to_integer((zlib_batch_count(n) + 16)) + adler_weighted_sum(old(buf), (zlib_batch_count(n) + 16), (zlib_batch_count(n) + 16)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_batch_count(n) + 16)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_batch_count(n) + 16)) by solve();

     apply(zlib_batch_prefix_step(n));
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     have to_integer(zlib_batch_count(n)) + to_integer(16) >= -2147483648 by solve() using { 0 <= to_integer(zlib_batch_count(n)); };
     have to_integer(zlib_batch_count(n)) + to_integer(16) <= 2147483647 by solve() using { to_integer(zlib_batch_count(n)) <= 5552; };
     have defined(zlib_batch_count(n) + 16);
     have defined(zlib_batch_count(n) + 16) by assumption();
     step_until(assignment(buf, 1));
     mark before_advance;
     step();
     have buf == at(before_advance, buf) + 16 by solve();
     have old(buf) + zlib_batch_count(n) + 16 == old(buf) + (zlib_batch_count(n) + 16) by normalize() using { defined(zlib_batch_count(n) + 16); };
     have buf == old(buf) + zlib_batch_count(n - 1u32) by solve() using {
      buf == at(before_advance, buf) + 16;
      at(before_advance, buf) == old(buf) + zlib_batch_count(n);
      old(buf) + zlib_batch_count(n) + 16 == old(buf) + (zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n - 1u32)) by solve() using {
      to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     have to_integer(sum2) == to_integer(zlib_batch_count(n - 1u32)) + adler_weighted_sum(old(buf), zlib_batch_count(n - 1u32), zlib_batch_count(n - 1u32)) by solve() using {
      to_integer(sum2) == to_integer(zlib_batch_count(n) + 16) + adler_weighted_sum(old(buf), zlib_batch_count(n) + 16, zlib_batch_count(n) + 16);
      zlib_batch_count(n - 1u32) == zlib_batch_count(n) + 16;
     };
     step(); step(); step();
     if n == 0u32 { step(); step(); } else {
      step(); step_until(back_edge());
      apply(zlib_batch_positive(n));
      have n <= 347u32 by assumption();
      have len == 0u64 by solve() using { at(batch_entry, len) == 5552u64; };
      have old(len) == 5552u64 by assumption();
      apply(zlib_batch_remaining_limit(n));
      unfold(zlib_batch_remaining(n));
      have 16u64 * n as uint64 <= 5552u64 by assumption();
      have 16u64 * n as uint64 <= 9223372036854775807u64 by solve() using { 16u64 * n as uint64 <= 5552u64; };
      apply(zlib_batch_cursor(old(buf), n));
      have buf == old(buf) + (5552u64 - zlib_batch_remaining(n)) by solve() using {
       buf == old(buf) + zlib_batch_count(n);
       old(buf) + zlib_batch_count(n) == old(buf) + (5552u64 - zlib_batch_remaining(n));
      };
      apply(zlib_batch_capacity_step(at(before_advance, n)));
      have n == at(before_advance, n) - 1u32 by solve();
      have 16u64 * n as uint64 == at(before_advance, 16u64 * n as uint64) - 16u64 by solve() using {
       n == at(before_advance, n) - 1u32;
       at(before_advance, 16u64 * (n - 1u32) as uint64) == at(before_advance, 16u64 * n as uint64 - 16u64);
      };
      have 16u64 * n as uint64 <= at(before_block, 16u64 * n as uint64) - 16u64 by solve() using {
       16u64 * n as uint64 == at(before_advance, 16u64 * n as uint64) - 16u64;
      };
      have buf == at(before_block, buf) + 16 by solve();
      have viewable(buf[0u64..16u64 * n as uint64]) by {
       transport(at(before_block, viewable(buf[0u64..16u64 * n as uint64])), viewable(buf[0u64..16u64 * n as uint64])) using {
        buf == at(before_block, buf) + 16;
        at(before_block, viewable(buf[0u64..16u64 * n as uint64]));
        16u64 <= at(before_advance, 16u64 * n as uint64);
        16u64 * n as uint64 <= at(before_block, 16u64 * n as uint64) - 16u64;
        16u64 * n as uint64 <= 5552u64;
        16u64 * n as uint64 <= 9223372036854775807u64;
       };
      }
      have zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16) by solve() using {
       n == at(before_advance, n) - 1u32;
       at(before_advance, zlib_batch_count(n - 1u32)) == at(before_advance, zlib_batch_count(n) + 16);
      };
      have adler == at(before_advance, adler) by solve();
      have sum2 == at(before_advance, sum2) by solve();
      have to_integer(adler) <= 1 + 255 * to_integer(zlib_batch_count(n)) by solve() using {
       adler == at(before_advance, adler);
       at(before_advance, to_integer(adler) <= 1 + 255 * to_integer(zlib_batch_count(n) + 16));
       zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16);
      };
      have to_integer(sum2) <= 1415761 * to_integer(zlib_batch_count(n)) by solve() using {
       sum2 == at(before_advance, sum2);
       at(before_advance, to_integer(sum2) <= 1415761 * to_integer(zlib_batch_count(n) + 16));
       zlib_batch_count(n) == at(before_advance, zlib_batch_count(n) + 16);
      };
      have 0 <= to_integer(n); have to_integer(n) <= 4294967295;
      have to_integer(at(before_advance, n) - 1u32) == to_integer(at(before_advance, n)) - to_integer(1u32);
      have to_integer(n) == at(before_advance, to_integer(n)) - 1 by solve() using {
       n == at(before_advance, n) - 1u32;
       to_integer(at(before_advance, n) - 1u32) == to_integer(at(before_advance, n)) - to_integer(1u32);
      };
      have to_integer(n) < at(before_advance, to_integer(n)) by solve() using {
       to_integer(n) == at(before_advance, to_integer(n)) - 1;
      };
      close_invariants() by assumption();
     }
    }
   }
   have n == 0u32 by solve();
   apply(zlib_batch_prefix_final());
   have zlib_batch_count(n) == 5552 by solve();
   have len == 0u64 by solve() using { at(batch_entry, len) == 5552u64; };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 5552) by solve() using {
    to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n));
    zlib_batch_count(n) == 5552;
   };
   have to_integer(zlib_batch_count(n)) == 5552 by solve() using { zlib_batch_count(n) == 5552; };
   have adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n)) == adler_weighted_sum(old(buf), 5552, 5552) by solve() using { zlib_batch_count(n) == 5552; };
   have to_integer(sum2) == to_integer(5552) + adler_weighted_sum(old(buf), 5552, 5552) by solve() using {
    to_integer(sum2) == to_integer(zlib_batch_count(n)) + adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n));
    to_integer(zlib_batch_count(n)) == 5552;
    adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n)) == adler_weighted_sum(old(buf), 5552, 5552);
   };
   apply(zlib_batch_reduced_components(old(buf), adler, sum2));
   mark before_reductions;
   step(); step();
   have adler == at(before_reductions, adler % 65521u64) by solve();
   have sum2 == at(before_reductions, sum2 % 65521u64) by solve();
   have to_integer(adler) == adler_spec_a(old(buf), 5552, 1) by solve() using {
    adler == at(before_reductions, adler % 65521u64);
    at(before_reductions, to_integer(adler % 65521u64)) == adler_spec_a(old(buf), 5552, 1);
   };
   have to_integer(sum2) == adler_spec_b(old(buf), 5552, 1, 0) by solve() using {
    sum2 == at(before_reductions, sum2 % 65521u64);
    at(before_reductions, to_integer(sum2 % 65521u64)) == adler_spec_b(old(buf), 5552, 1, 0);
   };
   apply(adler_spec_a_canonical(old(buf), 5552, 1));
   apply(adler_spec_b_canonical(old(buf), 5552, 1, 0));
   have to_integer(adler) <= 65520 by solve() using {
    to_integer(adler) == adler_spec_a(old(buf), 5552, 1);
    adler_spec_a(old(buf), 5552, 1) <= 65520;
   };
   have to_integer(sum2) <= 65520 by solve() using {
    to_integer(sum2) == adler_spec_b(old(buf), 5552, 1, 0);
    adler_spec_b(old(buf), 5552, 1, 0) <= 65520;
   };
   have adler <= 65520u64;
   have sum2 <= 65520u64;
   have buf == old(buf) + 5552 by solve() using {
    buf == old(buf) + zlib_batch_count(n);
    zlib_batch_count(n) == 5552;
   };
   have old(len) - len == 5552u64 by solve() using { old(len) == 5552u64; len == 0u64; };
   have buf == old(buf) + (old(len) - len) by solve() using {
    buf == old(buf) + 5552;
    old(len) - len == 5552u64;
   };
   have len <= 9223372036854775807u64 by solve() using { len == 0u64; };
   have viewable(buf[0u64..len]) by solve() using { len == 0u64; };
   have zlib_prefix_count(old(len), len) == 5552 by {
    unfold(zlib_prefix_count(old(len), len)); solve() using { old(len) == 5552u64; len == 0u64; };
   }
   have to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1) by solve() using {
    to_integer(adler) == adler_spec_a(old(buf), 5552, 1);
    zlib_prefix_count(old(len), len) == 5552;
   };
   have to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0) by solve() using {
    to_integer(sum2) == adler_spec_b(old(buf), 5552, 1, 0);
    zlib_prefix_count(old(len), len) == 5552;
   };
   have len == 5552u64 or len == 0u64 by assumption();
   have len <= 5552u64 by solve() using { len == 0u64; };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have to_integer(len) == 0 by solve() using { len == 0u64; };
   have at(batch_entry, to_integer(len)) == 5552 by solve() using { at(batch_entry, len) == 5552u64; };
   have to_integer(len) < at(batch_entry, to_integer(len)) by solve() using {
    to_integer(len) == 0;
    at(batch_entry, to_integer(len)) == 5552;
   };
   close_invariants() by assumption();
  }
 }
 have len < 5552u64 by assumption();
 have len == 0u64 by {
  cases {
   len == 5552u64 => {
    have not (len < 5552u64) by solve() using { len == 5552u64; };
    contradiction(len < 5552u64);
   }
   len == 0u64 => { assumption(); }
  }
 }
 have zlib_prefix_count(old(len), len) == 5552 by {
  unfold(zlib_prefix_count(old(len), len)); solve() using { old(len) == 5552u64; len == 0u64; };
 }
 have to_integer(adler) == adler_spec_a(old(buf), 5552, 1) by solve() using {
  to_integer(adler) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), 1);
  zlib_prefix_count(old(len), len) == 5552;
 };
 have to_integer(sum2) == adler_spec_b(old(buf), 5552, 1, 0) by solve() using {
  to_integer(sum2) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), 1, 0);
  zlib_prefix_count(old(len), len) == 5552;
 };
 have adler <= 65535u64 by solve() using { adler <= 65520u64; };
 have sum2 <= 65535u64 by solve() using { sum2 <= 65520u64; };
 apply(integer::uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), 5552, 1, 0) by {
  unfold(adler_spec_checksum(old(buf), 5552, 1, 0));
  solve() using {
   to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2);
   to_integer(adler) == adler_spec_a(old(buf), 5552, 1);
   to_integer(sum2) == adler_spec_b(old(buf), 5552, 1, 0);
  };
 }
}
