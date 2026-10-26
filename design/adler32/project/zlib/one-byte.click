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
 have adler + buf[0] as uint64 < 65521u64 by { rewrite(adler == 1u64); solve() using { buf[0] as uint64 <= 255u64; }; }
 step_until(assignment(adler, 1)); step();
 have adler == 1u64 + buf[0] as uint32 as uint64 by { solve(); }
 have adler <= 256u64 by { solve() using { buf[0] as uint32 as uint64 <= 255u64; adler == 1u64 + buf[0] as uint32 as uint64; }; }
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
 have to_integer(1u64) + to_integer(buf[0] as uint32 as uint64) <= 18446744073709551615 by { solve() using { to_integer(buf[0] as uint32 as uint64) == to_integer(buf[0] as int32); to_integer(buf[0] as int32) <= 255; }; }
 have to_integer(1u64 + buf[0] as uint32 as uint64) == to_integer(1u64) + to_integer(buf[0] as uint32 as uint64);
 have to_integer(adler) == 1 + to_integer(buf[0] as int32) by { rewrite(adler == 1u64 + buf[0] as uint32 as uint64); rewrite(to_integer(1u64 + buf[0] as uint32 as uint64) == to_integer(1u64) + to_integer(buf[0] as uint32 as uint64)); rewrite(to_integer(buf[0] as uint32 as uint64) == to_integer(buf[0] as int32)); solve(); }
 apply(adler_spec_one(buf));
 have 0 <= 1 + to_integer(buf[0] as int32) by { solve() using { 0 <= to_integer(buf[0] as int32); }; }
 have 1 + to_integer(buf[0] as int32) < 65521 by { solve() using { to_integer(buf[0] as int32) <= 255; }; }
 have 1 + to_integer(buf[0] as int32) <= 65520 by { solve() using { to_integer(buf[0] as int32) <= 255; }; }
 have 1 + to_integer(buf[0] as int32) == 0 * 65521 + (1 + to_integer(buf[0] as int32)) by { solve() using {}; }
 apply(adler_residue_unique(1 + to_integer(buf[0] as int32), 0, 1 + to_integer(buf[0] as int32)));

 apply(zlib_pack_order(1 + to_integer(buf[0] as int32)));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(buf, 1, 1, 0) by {
  unfold(adler_spec_checksum(buf, 1, 1, 0));
  rewrite(adler_spec_a(buf, 1, 1) == truncating_remainder(1 + to_integer(buf[0] as int32), 65521));
  rewrite(adler_spec_b(buf, 1, 1, 0) == truncating_remainder(1 + to_integer(buf[0] as int32), 65521));
  rewrite(truncating_remainder(1 + to_integer(buf[0] as int32), 65521) == 1 + to_integer(buf[0] as int32));
  rewrite(to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2));
  rewrite(sum2 == adler);
  rewrite(to_integer(adler) == 1 + to_integer(buf[0] as int32));
  assumption();
 }
 have to_integer(1) == to_integer(1u64) by normalize();
 apply(adler_spec_checksum_bridge(buf, 1, 1u64, 1, 0)) using { to_integer(1) == to_integer(1u64); };
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum_u64(buf, 1u64, 1, 0) by {
  rewrite(adler_spec_checksum_u64(buf, 1u64, 1, 0) == adler_spec_checksum(buf, 1, 1, 0));
  assumption();
 }
}
