import click::integer;

target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "../adler32-spec-bridge.click";
theorem zlib_pack_order(value: Integer) {
 ensures value + 65536 * value == 65536 * value + value by { solve() using {}; }
}
import "byte.click";
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires adler == 1u64;
 requires len == 1u64;
 requires buf != 0;
 views buf[0u64..1u64];
 ensures result == (old(1u64 + buf[0]) | (old(1u64 + buf[0]) << 16i64));
 ensures buf[0] == old(buf[0]);
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 1u64, 1, 0);
} by {
 step_until(assignment(adler, 0)); step();
 have adler == 1u64 by { solve(); }
 have sum2 == 0u64 by { solve(); }
 apply(zlib_byte_u64(buf[0]));
 have adler + (uint64)buf[0] < 65521u64 by { rewrite(adler == 1u64); solve() using { (uint64)buf[0] <= 255u64; }; }
 step_until(assignment(adler, 1)); step();
 have adler == 1u64 + (uint64)(uint32)buf[0] by { solve(); }
 have adler <= 256u64 by { solve() using { (uint64)(uint32)buf[0] <= 255u64; adler == 1u64 + (uint64)(uint32)buf[0]; }; }
 have adler < 65521u64 by { solve() using { adler <= 256u64; }; }
 apply(integer::uint64_less_than_implies_not_greater_equal(adler, 65521u64));
 step_until(assignment(sum2, 1)); step();
 have sum2 == adler by { solve(); }
 have sum2 <= 256u64 by { rewrite(sum2 == adler); assumption(); }
 have sum2 < 65521u64 by { solve() using { sum2 <= 256u64; }; }
 apply(integer::uint64_less_than_implies_not_greater_equal(sum2, 65521u64));
 have adler <= 65535u64 by { solve() using { adler <= 256u64; }; }
 have sum2 <= 65535u64 by { solve() using { sum2 <= 256u64; }; }
 apply(integer::uint64_pack_uint16_to_integer(adler, sum2));
 have to_integer(1u64) + to_integer((uint64)(uint32)buf[0]) <= 18446744073709551615 by { solve() using { to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0]); to_integer((int32)buf[0]) <= 255; }; }
 have to_integer(1u64 + (uint64)(uint32)buf[0]) == to_integer(1u64) + to_integer((uint64)(uint32)buf[0]);
 have to_integer(adler) == 1 + to_integer((int32)buf[0]) by { rewrite(adler == 1u64 + (uint64)(uint32)buf[0]); rewrite(to_integer(1u64 + (uint64)(uint32)buf[0]) == to_integer(1u64) + to_integer((uint64)(uint32)buf[0])); rewrite(to_integer((uint64)(uint32)buf[0]) == to_integer((int32)buf[0])); solve(); }
 apply(adler_spec_one(buf));
 have 0 <= 1 + to_integer((int32)buf[0]) by { solve() using { 0 <= to_integer((int32)buf[0]); }; }
 have 1 + to_integer((int32)buf[0]) < 65521 by { solve() using { to_integer((int32)buf[0]) <= 255; }; }
 have 1 + to_integer((int32)buf[0]) <= 65520 by { solve() using { to_integer((int32)buf[0]) <= 255; }; }
 have 1 + to_integer((int32)buf[0]) == 0 * 65521 + (1 + to_integer((int32)buf[0])) by { solve() using {}; }
 apply(adler_residue_unique(1 + to_integer((int32)buf[0]), 0, 1 + to_integer((int32)buf[0])));

 apply(zlib_pack_order(1 + to_integer((int32)buf[0])));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(buf, 1, 1, 0) by {
  unfold(adler_spec_checksum(buf, 1, 1, 0));
  rewrite(adler_spec_a(buf, 1, 1) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(adler_spec_b(buf, 1, 1, 0) == truncating_remainder(1 + to_integer((int32)buf[0]), 65521));
  rewrite(truncating_remainder(1 + to_integer((int32)buf[0]), 65521) == 1 + to_integer((int32)buf[0]));
  rewrite(to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2));
  rewrite(sum2 == adler);
  rewrite(to_integer(adler) == 1 + to_integer((int32)buf[0]));
  assumption();
 }
 have to_integer(1) == to_integer(1u64) by normalize();
 apply(adler_spec_checksum_bridge(buf, 1, 1u64, 1, 0)) using { to_integer(1) == to_integer(1u64); };
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum_u64(buf, 1u64, 1, 0) by {
  rewrite(adler_spec_checksum_u64(buf, 1u64, 1, 0) == adler_spec_checksum(buf, 1, 1, 0));
  assumption();
 }
 execute(); solve();
}
