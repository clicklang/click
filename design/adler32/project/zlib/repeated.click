import click::integer;

target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "window.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires 16u64 <= len;
 requires len <= 5551u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
 have to_integer(len as uint32 as int32) == to_integer(len) by {
  arithmetic_certificate rules {
   premise 0: 0 <= to_integer(len) => 0 <= to_integer(len);
   premise 1: to_integer(len) <= 2147483647 => to_integer(len) <= 2147483647;
   integer_cast_identity bounds [0, 1] => to_integer(len as uint32 as int32) == to_integer(len);
   conclusion 0;
  }
 }
 apply(adler_spec_checksum_bridge(buf, len as uint32 as int32, len, 1, 0)) using { to_integer(len as uint32 as int32) == to_integer(len); };
 have viewable(buf[0u64..len]) by solve();
 step_until(loop(3));
 have viewable(buf[0u64..len]) by solve();
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant len <= old(len);
  invariant old(len) <= 5551u64;
  invariant old(len) - len <= 5551u64;
  invariant to_integer(len) <= 5551;
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));
  invariant to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len));
  initialize by {
   have len <= old(len) by solve();
   have old(len) - len == 0u64 by solve();
   have adler == 1u64 by solve();
   have sum2 == 0u64 by solve();
   have to_integer(adler) == 1 by solve() using { adler == 1u64; };
   have to_integer(sum2) == 0 by solve() using { sum2 == 0u64; };
   have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); solve(); }
   apply(adler_sum_empty(old(buf), 0));
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 0) by solve() using { to_integer(adler) == 1; adler_byte_sum(old(buf), 0) == 0; };
   have to_integer(sum2) == to_integer(0) + adler_weighted_sum(old(buf), 0, 0) by solve() using { to_integer(sum2) == 0; adler_weighted_sum(old(buf), 0, 0) == 0; };
   have to_integer(adler) <= 1 + 255 * to_integer(0) by solve() using { to_integer(adler) == 1; };
   have to_integer(sum2) <= 1415761 * to_integer(0) by solve() using { to_integer(sum2) == 0; };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == 0); assumption(); }
   solve();
  }
  preserve by {
   have 16u64 <= len by solve();
   have len <= 5551u64 by solve() using { len <= old(len); old(len) <= 5551u64; };
   have len <= 9223372036854775807u64 by solve() using { len <= 5551u64; };
   have 1u64 <= len by solve() using { 16u64 <= len; };
   have viewable(buf[0u64..16u64]) by solve();
   apply(zlib_remaining_step(old(len), len, 16u64));
   have old(len) - len <= 22208u64 by solve() using { old(len) - len <= 5551u64; };
   apply(zlib_prefix_observation(old(len), len));
   have old(len) - len < old(len) by solve() using { 16u64 <= len; len <= old(len); old(len) <= 5551u64; };
   mark before_block;
   step();
   have len == at(before_block, len - 16u64) by solve();
   have to_integer(len) == at(before_block, to_integer(len)) - 16 by solve();
   step_until(assignment(adler, 22));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 0u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 0)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 0));
   have buf[0] == old(buf)[zlib_prefix_count(old(len), at(before_block, len))] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[0] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 0];
   };
   apply(zlib_native_component_step(old(buf), zlib_prefix_count(old(len), at(before_block, len)), adler, sum2, buf[0]));
   have viewable(buf[0u64..1u64]) by solve();
   mark byte_0;
   step();
   step_until(assignment(sum2, 22));
   step();
   have adler == at(byte_0, adler + buf[0] as uint32 as uint64) by solve();
   have sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1) by solve() using {
    adler == at(byte_0, adler + buf[0] as uint32 as uint64);
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1);
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1, zlib_prefix_count(old(len), at(before_block, len)) + 1) by solve() using {
    sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1, zlib_prefix_count(old(len), at(before_block, len)) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) by solve() using {
    adler == at(byte_0, adler + buf[0] as uint32 as uint64);
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) by solve() using {
    sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) <= 1415761 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1), (zlib_prefix_count(old(len), at(before_block, len)) + 1)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) by solve();
   step_until(assignment(adler, 23));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 1u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 1)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 1));
   have buf[1] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 1)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[1] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 1];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1), adler, sum2, buf[1]));
   mark byte_1;
   step();
   step_until(assignment(sum2, 23));
   step();
   have adler == at(byte_1, adler + buf[1] as uint32 as uint64) by solve();
   have sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by solve() using {
    adler == at(byte_1, adler + buf[1] as uint32 as uint64);
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by solve() using {
    sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by solve() using {
    adler == at(byte_1, adler + buf[1] as uint32 as uint64);
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by solve() using {
    sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2), (zlib_prefix_count(old(len), at(before_block, len)) + 2)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) by solve();
   step_until(assignment(adler, 24));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 2u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 2)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 2));
   have buf[2] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 2)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[2] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 2];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2), adler, sum2, buf[2]));
   mark byte_2;
   step();
   step_until(assignment(sum2, 24));
   step();
   have adler == at(byte_2, adler + buf[2] as uint32 as uint64) by solve();
   have sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by solve() using {
    adler == at(byte_2, adler + buf[2] as uint32 as uint64);
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by solve() using {
    sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by solve() using {
    adler == at(byte_2, adler + buf[2] as uint32 as uint64);
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by solve() using {
    sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3), (zlib_prefix_count(old(len), at(before_block, len)) + 3)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) by solve();
   step_until(assignment(adler, 25));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 3u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 3)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 3));
   have buf[3] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 3)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[3] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 3];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3), adler, sum2, buf[3]));
   mark byte_3;
   step();
   step_until(assignment(sum2, 25));
   step();
   have adler == at(byte_3, adler + buf[3] as uint32 as uint64) by solve();
   have sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by solve() using {
    adler == at(byte_3, adler + buf[3] as uint32 as uint64);
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by solve() using {
    sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by solve() using {
    adler == at(byte_3, adler + buf[3] as uint32 as uint64);
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by solve() using {
    sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4), (zlib_prefix_count(old(len), at(before_block, len)) + 4)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) by solve();
   step_until(assignment(adler, 26));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 4u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 4)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 4));
   have buf[4] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 4)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[4] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 4];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4), adler, sum2, buf[4]));
   mark byte_4;
   step();
   step_until(assignment(sum2, 26));
   step();
   have adler == at(byte_4, adler + buf[4] as uint32 as uint64) by solve();
   have sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by solve() using {
    adler == at(byte_4, adler + buf[4] as uint32 as uint64);
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by solve() using {
    sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by solve() using {
    adler == at(byte_4, adler + buf[4] as uint32 as uint64);
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by solve() using {
    sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5), (zlib_prefix_count(old(len), at(before_block, len)) + 5)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) by solve();
   step_until(assignment(adler, 27));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 5u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 5)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 5));
   have buf[5] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 5)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[5] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 5];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5), adler, sum2, buf[5]));
   mark byte_5;
   step();
   step_until(assignment(sum2, 27));
   step();
   have adler == at(byte_5, adler + buf[5] as uint32 as uint64) by solve();
   have sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by solve() using {
    adler == at(byte_5, adler + buf[5] as uint32 as uint64);
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by solve() using {
    sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by solve() using {
    adler == at(byte_5, adler + buf[5] as uint32 as uint64);
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by solve() using {
    sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6), (zlib_prefix_count(old(len), at(before_block, len)) + 6)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) by solve();
   step_until(assignment(adler, 28));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 6u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 6)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 6));
   have buf[6] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 6)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[6] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 6];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6), adler, sum2, buf[6]));
   mark byte_6;
   step();
   step_until(assignment(sum2, 28));
   step();
   have adler == at(byte_6, adler + buf[6] as uint32 as uint64) by solve();
   have sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by solve() using {
    adler == at(byte_6, adler + buf[6] as uint32 as uint64);
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by solve() using {
    sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by solve() using {
    adler == at(byte_6, adler + buf[6] as uint32 as uint64);
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by solve() using {
    sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7), (zlib_prefix_count(old(len), at(before_block, len)) + 7)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) by solve();
   step_until(assignment(adler, 29));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 7u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 7)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 7));
   have buf[7] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 7)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[7] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 7];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7), adler, sum2, buf[7]));
   mark byte_7;
   step();
   step_until(assignment(sum2, 29));
   step();
   have adler == at(byte_7, adler + buf[7] as uint32 as uint64) by solve();
   have sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by solve() using {
    adler == at(byte_7, adler + buf[7] as uint32 as uint64);
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by solve() using {
    sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by solve() using {
    adler == at(byte_7, adler + buf[7] as uint32 as uint64);
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by solve() using {
    sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8), (zlib_prefix_count(old(len), at(before_block, len)) + 8)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) by solve();
   step_until(assignment(adler, 30));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 8u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 8)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 8));
   have buf[8] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 8)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[8] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 8];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8), adler, sum2, buf[8]));
   mark byte_8;
   step();
   step_until(assignment(sum2, 30));
   step();
   have adler == at(byte_8, adler + buf[8] as uint32 as uint64) by solve();
   have sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by solve() using {
    adler == at(byte_8, adler + buf[8] as uint32 as uint64);
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by solve() using {
    sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by solve() using {
    adler == at(byte_8, adler + buf[8] as uint32 as uint64);
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by solve() using {
    sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9), (zlib_prefix_count(old(len), at(before_block, len)) + 9)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) by solve();
   step_until(assignment(adler, 31));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 9u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 9)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 9));
   have buf[9] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 9)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[9] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 9];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9), adler, sum2, buf[9]));
   mark byte_9;
   step();
   step_until(assignment(sum2, 31));
   step();
   have adler == at(byte_9, adler + buf[9] as uint32 as uint64) by solve();
   have sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by solve() using {
    adler == at(byte_9, adler + buf[9] as uint32 as uint64);
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by solve() using {
    sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by solve() using {
    adler == at(byte_9, adler + buf[9] as uint32 as uint64);
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by solve() using {
    sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10), (zlib_prefix_count(old(len), at(before_block, len)) + 10)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) by solve();
   step_until(assignment(adler, 32));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 10u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 10)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 10));
   have buf[10] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 10)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[10] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 10];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10), adler, sum2, buf[10]));
   mark byte_10;
   step();
   step_until(assignment(sum2, 32));
   step();
   have adler == at(byte_10, adler + buf[10] as uint32 as uint64) by solve();
   have sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by solve() using {
    adler == at(byte_10, adler + buf[10] as uint32 as uint64);
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by solve() using {
    sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by solve() using {
    adler == at(byte_10, adler + buf[10] as uint32 as uint64);
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by solve() using {
    sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11), (zlib_prefix_count(old(len), at(before_block, len)) + 11)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) by solve();
   step_until(assignment(adler, 33));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 11u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 11)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 11));
   have buf[11] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 11)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[11] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 11];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11), adler, sum2, buf[11]));
   mark byte_11;
   step();
   step_until(assignment(sum2, 33));
   step();
   have adler == at(byte_11, adler + buf[11] as uint32 as uint64) by solve();
   have sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by solve() using {
    adler == at(byte_11, adler + buf[11] as uint32 as uint64);
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by solve() using {
    sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by solve() using {
    adler == at(byte_11, adler + buf[11] as uint32 as uint64);
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by solve() using {
    sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12), (zlib_prefix_count(old(len), at(before_block, len)) + 12)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) by solve();
   step_until(assignment(adler, 34));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 12u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 12)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 12));
   have buf[12] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 12)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[12] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 12];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12), adler, sum2, buf[12]));
   mark byte_12;
   step();
   step_until(assignment(sum2, 34));
   step();
   have adler == at(byte_12, adler + buf[12] as uint32 as uint64) by solve();
   have sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by solve() using {
    adler == at(byte_12, adler + buf[12] as uint32 as uint64);
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by solve() using {
    sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by solve() using {
    adler == at(byte_12, adler + buf[12] as uint32 as uint64);
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by solve() using {
    sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13), (zlib_prefix_count(old(len), at(before_block, len)) + 13)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) by solve();
   step_until(assignment(adler, 35));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 13u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 13)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 13));
   have buf[13] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 13)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[13] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 13];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13), adler, sum2, buf[13]));
   mark byte_13;
   step();
   step_until(assignment(sum2, 35));
   step();
   have adler == at(byte_13, adler + buf[13] as uint32 as uint64) by solve();
   have sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by solve() using {
    adler == at(byte_13, adler + buf[13] as uint32 as uint64);
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by solve() using {
    sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by solve() using {
    adler == at(byte_13, adler + buf[13] as uint32 as uint64);
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by solve() using {
    sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14), (zlib_prefix_count(old(len), at(before_block, len)) + 14)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) by solve();
   step_until(assignment(adler, 36));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 14u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 14)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 14));
   have buf[14] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 14)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[14] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 14];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14), adler, sum2, buf[14]));
   mark byte_14;
   step();
   step_until(assignment(sum2, 36));
   step();
   have adler == at(byte_14, adler + buf[14] as uint32 as uint64) by solve();
   have sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by solve() using {
    adler == at(byte_14, adler + buf[14] as uint32 as uint64);
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by solve() using {
    sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by solve() using {
    adler == at(byte_14, adler + buf[14] as uint32 as uint64);
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by solve() using {
    sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15), (zlib_prefix_count(old(len), at(before_block, len)) + 15)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) by solve();
   step_until(assignment(adler, 37));
   apply(zlib_block_read_bound(old(len), at(before_block, len), 15u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 15)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 15));
   have buf[15] == old(buf)[(zlib_prefix_count(old(len), at(before_block, len)) + 15)] by solve() using {
    buf == old(buf) + (old(len) - at(before_block, len));
    (old(buf) + (old(len) - at(before_block, len)))[15] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 15];
   };
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15), adler, sum2, buf[15]));
   mark byte_15;
   step();
   step_until(assignment(sum2, 37));
   step();
   have adler == at(byte_15, adler + buf[15] as uint32 as uint64) by solve();
   have sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)) by solve();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by solve() using {
    adler == at(byte_15, adler + buf[15] as uint32 as uint64);
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by solve() using {
    sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by solve() using {
    adler == at(byte_15, adler + buf[15] as uint32 as uint64);
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by solve() using {
    sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 16)) by solve();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 16), (zlib_prefix_count(old(len), at(before_block, len)) + 16)) by solve();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) by solve();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) by solve();
   step_until(back_edge());
   have len <= old(len) by solve();
   have old(len) - len <= 5551u64 by solve();
   have to_integer(len) <= 5551 by solve() using { to_integer(len) == at(before_block, to_integer(len)) - 16; at(before_block, to_integer(len)) <= 5551; };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have len <= 5551u64;
   have len <= 9223372036854775807u64 by solve() using { len <= 5551u64; };
   have to_integer(len) < at(before_block, to_integer(len)) by solve() using { to_integer(len) == at(before_block, to_integer(len)) - 16; };
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + 16 by solve();
   have -2147483648 <= to_integer(zlib_prefix_count(old(len), len)); have to_integer(zlib_prefix_count(old(len), len)) <= 2147483647;
   have -2147483648 <= to_integer(zlib_prefix_count(old(len), at(before_block, len))); have to_integer(zlib_prefix_count(old(len), at(before_block, len))) <= 2147483647;
   have to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16) >= -2147483648 by solve() using { -2147483648 <= to_integer(zlib_prefix_count(old(len), at(before_block, len))); };
   have to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16) <= 2147483647 by solve() using { to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + 16; to_integer(zlib_prefix_count(old(len), len)) <= 2147483647; };
   have defined(zlib_prefix_count(old(len), at(before_block, len)) + 16);
   have defined(zlib_prefix_count(old(len), at(before_block, len)) + 16) by assumption();
   have to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16);
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16) by solve() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + 16;
    to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16);
   };
   have buf == at(before_block, buf) + 16 by solve();
   have old(len) - len == (old(len) - at(before_block, len)) + 16u64 by solve() using {
    len == at(before_block, len - 16u64);
    16u64 <= at(before_block, len);
    at(before_block, len) <= old(len);
    old(len) <= 5551u64;
   };
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf == at(before_block, buf) + 16);
    rewrite(old(len) - len == (old(len) - at(before_block, len)) + 16u64);
    arithmetic_certificate rules {
     premise 0: at(before_block, buf) == old(buf) + (old(len) - at(before_block, len)) => at(before_block, buf) == old(buf) + (old(len) - at(before_block, len));
     premise 1: old(len) - at(before_block, len) <= 5535u64 => old(len) - at(before_block, len) <= 5535u64;
     pointer_translation relation 0 bounds [1] => at(before_block, buf) + 16 == old(buf) + ((old(len) - at(before_block, len)) + 16u64);
     conclusion 0;
    }
   }
   have len <= at(before_block, len) - 16u64 by solve();
   have viewable(buf[0u64..len]) by {
    transport(at(before_block, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     buf == at(before_block, buf) + 16;
     at(before_block, viewable(buf[0u64..len]));
     16u64 <= at(before_block, len);
     len <= at(before_block, len) - 16u64;
     len <= 5551u64;
     len <= 9223372036854775807u64;
    };
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16); assumption(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16); assumption(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16); assumption(); }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len) == zlib_prefix_count(old(len), at(before_block, len)) + 16); assumption(); }
   close_invariants() by assumption();
  }
 }
 have len <= 15u64 by solve() using { not (len >= 16u64); len <= old(len); old(len) <= 5551u64; };
 have to_integer(len) <= to_integer(15u64);
 step_until(loop(4));
 have to_integer(old(len)) <= to_integer(5551u64);
 have to_integer(len) <= to_integer(old(len));
 have to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
 have old(len) - len <= 22208u64 by solve() using { old(len) - len <= 5551u64; };
 apply(zlib_prefix_observation(old(len), len));
 apply(adler_sum_nonnegative(old(buf), zlib_prefix_count(old(len), len)));
 have 1 <= to_integer(adler) by solve() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); 0 <= adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); };
 have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
 have 0 <= to_integer(sum2); have to_integer(sum2) <= 18446744073709551615;
 have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by solve() using {
  to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len));
  to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
  to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
 };
 have to_integer(adler) <= 1415761 by solve() using { to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)); to_integer(old(len)) <= 5551; 0 <= to_integer(len); };
 have to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)) by solve() using {
  to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len));
  to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
  to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
 };
 have to_integer(sum2) <= 7858889311 by solve() using { to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)); to_integer(old(len)) <= 5551; 0 <= to_integer(len); };
// The scalar tail inherits the caller's complete input view. Its prefix
 // invariants locate each original read within that unchanged range.
 loop {
  decreases to_integer(len);
  invariant to_integer(len) <= 15;
  invariant to_integer(old(len)) <= 5551;
  invariant len <= old(len);
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant old(len) - len <= 5551u64;
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));
  invariant 1 <= to_integer(adler);
  invariant to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(adler) <= 1415761;
  invariant 0 <= to_integer(sum2);
  invariant to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len));
  invariant to_integer(sum2) <= 7858889311;
  initialize by { solve(); }
  preserve by {
   if len == 0u64 {
    have old(len) - len == old(len) by solve();
    have zlib_prefix_count(old(len), len) == old(len as uint32 as int32) by {
     unfold(zlib_prefix_count(old(len), len));
     solve();
    }
    have to_integer(adler) == 1 + adler_byte_sum(old(buf), old(len as uint32 as int32)) by {
     solve() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    have to_integer(sum2) == to_integer(old(len as uint32 as int32)) + adler_weighted_sum(old(buf), old(len as uint32 as int32), old(len as uint32 as int32)) by {
     solve() using { to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    step(); step(); step(); step();
    have __click_call_result4 == 0u64 by assumption();
    step();
   } else {
    have 0u64 <= len by normalize();
    have 0u64 < len by {
     if 0u64 < len { assumption(); } else {
      have 0u64 == len;
      have len == 0u64 by { rewrite(0u64 == len); normalize(); }
      contradiction(len == 0u64);
     }
    }
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have to_integer(0u64) < to_integer(len);
   have to_integer(1u64) <= to_integer(len) by solve() using { to_integer(0u64) < to_integer(len); };
   have 1u64 <= len;
   have to_integer(len - 1u64) == to_integer(len) - to_integer(1u64);
   have len <= 15u64;
   have viewable(buf[0u64..1u64]) by solve();
   have viewable(buf[0u64..len]) by solve();
   mark before_decrement;
   step(); step(); step(); step(); step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by assumption();
   have to_integer(len) <= 15 by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by solve() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   step_until(assignment(adler, 38));
   have __click_call_result3 == at(before_decrement, buf) by solve();
   have viewable(__click_call_result3[0u64..1u64]) by {
    solve() using { __click_call_result3 == at(before_decrement, buf); at(before_decrement, viewable(buf[0u64..1u64])); };
   }
   have __click_call_result3 == old(buf) + (old(len) - at(before_decrement, len)) by solve();
   have at(before_decrement, len) <= old(len) by assumption();
   have to_integer(at(before_decrement, len)) <= to_integer(old(len));
   have to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - to_integer(at(before_decrement, len));
   have to_integer(old(len) - at(before_decrement, len)) < to_integer(old(len)) by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) < old(len);
   have old(len) <= 5551u64;
   have to_integer(old(len) - at(before_decrement, len)) <= 5550 by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) <= 5550u64;
   have old(len) - at(before_decrement, len) <= 22208u64 by solve() using { old(len) - at(before_decrement, len) <= 5550u64; };
   have old(len) - at(before_decrement, len) <= 5551u64 by solve() using { old(len) - at(before_decrement, len) <= 5550u64; };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_decrement, len)));
   have __click_call_result3 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) by solve() using {
    __click_call_result3 == old(buf) + (old(len) - at(before_decrement, len));
    old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have __click_call_result3[0] == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))] by solve() using {
    __click_call_result3 == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_byte_u64(__click_call_result3[0]));
   apply(zlib_byte_integer_identity(__click_call_result3[0]));
   have to_integer(adler) <= 1415251 by solve() using {
    to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(adler) + to_integer(__click_call_result3[0] as uint32 as uint64) <= 18446744073709551615 by solve() using {
    to_integer(adler) <= 1415251;
    to_integer(__click_call_result3[0] as uint32 as uint64) == to_integer(__click_call_result3[0] as int32);
    to_integer(__click_call_result3[0] as int32) <= 255;
   };
   have to_integer(adler + __click_call_result3[0] as uint32 as uint64) == to_integer(adler) + to_integer(__click_call_result3[0] as uint32 as uint64);
   mark before_add;
   step();
   have adler == at(before_add, adler + __click_call_result3[0] as uint32 as uint64) by solve();
   have to_integer(adler) == at(before_add, to_integer(adler + __click_call_result3[0] as uint32 as uint64)) by solve() using { adler == at(before_add, adler + __click_call_result3[0] as uint32 as uint64); };
   have to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as int32)) by solve() using {
    to_integer(adler) == at(before_add, to_integer(adler + __click_call_result3[0] as uint32 as uint64));
    at(before_add, to_integer(adler + __click_call_result3[0] as uint32 as uint64)) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as uint32 as uint64));
    at(before_add, to_integer(__click_call_result3[0] as uint32 as uint64)) == at(before_add, to_integer(__click_call_result3[0] as int32));
   };
   have 1 <= to_integer(adler) by solve() using {
    1 <= at(before_add, to_integer(adler));
    0 <= at(before_add, to_integer(__click_call_result3[0] as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as int32));
   };
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by solve() using {
    at(before_add, to_integer(adler)) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    at(before_add, to_integer(__click_call_result3[0] as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as int32));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(adler) <= 1415761 by solve() using {
    at(before_add, to_integer(adler)) <= 1415251;
    at(before_add, to_integer(__click_call_result3[0] as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as int32));
   };
   have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by solve() using {
    to_integer(sum2) <= 7858889311;
    to_integer(adler) <= 1415761;
   };
   have to_integer(sum2 + adler) == to_integer(sum2) + to_integer(adler);
   mark before_sum;
   step_until(back_edge());
   have to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler) by solve();
   have 0 <= to_integer(sum2);
   have to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)) by solve() using {
    at(before_sum, to_integer(sum2)) <= 1415761 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(adler) <= 1415761;
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(sum2) <= 7858889311 by solve() using {
    to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len));
    to_integer(old(len)) <= 5551;
    0 <= to_integer(len);
   };
   have to_integer(len) <= to_integer(old(len)) by solve() using {
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have len <= old(len);
   have to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
   have to_integer(old(len) - at(before_decrement, len)) <= 5550 by solve() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) <= 5550u64;
   have to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64) <= 18446744073709551615 by solve() using { to_integer(old(len) - at(before_decrement, len)) <= 5550; };
   have to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   have to_integer(old(len) - len) == to_integer((old(len) - at(before_decrement, len)) + 1u64) by solve() using {
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   };
   have (old(len) - len) == ((old(len) - at(before_decrement, len)) + 1u64);
   have buf == at(before_decrement, buf) + 1 by solve();
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf == at(before_decrement, buf) + 1);
    rewrite(old(len) - len == (old(len) - at(before_decrement, len)) + 1u64);
    arithmetic_certificate rules {
     premise 0: at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len)) => at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
     premise 1: old(len) - at(before_decrement, len) <= 5550u64 => old(len) - at(before_decrement, len) <= 5550u64;
     pointer_translation relation 0 bounds [1] => at(before_decrement, buf) + 1 == old(buf) + ((old(len) - at(before_decrement, len)) + 1u64);
     conclusion 0;
    }
   }
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by solve();
   have len == (at(before_decrement, len) - 1u64);
   have len <= at(before_decrement, len) - 1u64 by solve();
   have len <= 15u64;
   have len <= 9223372036854775807u64;
   have viewable(buf[0u64..len]) by {
    transport(at(before_decrement, viewable(buf[0u64..len])), viewable(buf[0u64..len])) using {
     buf == at(before_decrement, buf) + 1;
     at(before_decrement, viewable(buf[0u64..len]));
     1u64 <= at(before_decrement, len);
     len <= at(before_decrement, len) - 1u64;
     len <= 15u64;
     len <= 9223372036854775807u64;
    };
   }
   have old(len) - len <= 5551u64 by {
    have to_integer(old(len) - len) <= 5551 by solve() using {
     to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
     to_integer(old(len)) <= 5551;
     0 <= to_integer(len);
    };
    have (old(len) - len) <= 5551u64;
   }
   have old(len) - len <= 22208u64 by solve() using { old(len) - len <= 5551u64; };
   apply(zlib_prefix_observation(old(len), len));
   apply(zlib_prefix_observation(old(len), at(before_decrement, len)));
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1 by solve() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };

   have 0 < to_integer(zlib_prefix_count(old(len), len)) by solve() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(1) <= to_integer(zlib_prefix_count(old(len), len)) by solve() using { 0 < to_integer(zlib_prefix_count(old(len), len)); };
   have 1 <= zlib_prefix_count(old(len), len);
   apply(zlib_positive_count(zlib_prefix_count(old(len), len)));
   have defined(zlib_prefix_count(old(len), len) - 1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   apply(zlib_prefix_append(old(buf), old(len), len));
   apply(adler_weighted_prefix_step(old(buf), zlib_prefix_count(old(len), len)));
   have old(buf)[zlib_prefix_count(old(len), len) - 1] == at(before_add, __click_call_result3[0]) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
    at(before_add, __click_call_result3[0]) == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))];
   };
   have adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len))) by solve() using {
    zlib_prefix_count(old(len), len) - 1 == zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_equal_byte_integers(old(buf)[zlib_prefix_count(old(len), len) - 1], at(before_add, __click_call_result3[0])));
   have zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(__click_call_result3[0] as int32)) by solve() using {
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == zlib_byte_integer(at(before_add, __click_call_result3[0]));
    at(before_add, zlib_byte_integer(__click_call_result3[0])) == at(before_add, to_integer(__click_call_result3[0] as int32));
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by solve() using {
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) + zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]);
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(__click_call_result3[0] as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(__click_call_result3[0] as int32));
    at(before_add, to_integer(adler)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by solve() using {
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    at(before_sum, to_integer(sum2)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len)));
    to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   }
  }
 }
 step_until(assignment(adler, 39));
 apply(zlib_reduced_result(old(buf), old(len as uint32 as int32), adler, sum2));
}
