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
  close() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
 }
 apply(adler_spec_checksum_bridge(buf, len as uint32 as int32, len, 1, 0));
 have viewable(buf[0u64..len]) by close();
 step();
 have separate(statement(0).footprint, memory(buf[0u64..len])) by close();
 have viewable(buf[0u64..len]) by {
  preserve(memory(buf[0u64..len]), statement(0));
 }
 step();
 have separate(statement(1).footprint, memory(buf[0u64..len])) by close();
 have viewable(buf[0u64..len]) by {
  preserve(memory(buf[0u64..len]), statement(1));
 }
 step();
 have separate(statement(2).footprint, memory(buf[0u64..len])) by close();
 have viewable(buf[0u64..len]) by {
  preserve(memory(buf[0u64..len]), statement(2));
 }
 step_until(loop(3).entry);
 have viewable(buf[0u64..len]) by close();
 loop {
  decreases to_integer(len);
  views buf[0u64..len];
  invariant len <= old(len);
  invariant old(len) <= 5551u64;
  invariant old(len) - len <= 5551u64;
  invariant to_integer(len) <= 5551;
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] };
  invariant forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
  invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));
  invariant to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len));
  invariant to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len));
  initialize by {
   have len <= old(len) by close();
   have old(len) - len == 0u64 by close();
   have adler == 1u64 by close();
   have sum2 == 0u64 by close();
   have to_integer(adler) == 1 by close() using { adler == 1u64; };
   have to_integer(sum2) == 0 by close() using { sum2 == 0u64; };
   have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); close(); }
   apply(adler_sum_empty(old(buf), 0));
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), 0) by close() using { to_integer(adler) == 1; adler_byte_sum(old(buf), 0) == 0; };
   have to_integer(sum2) == to_integer(0) + adler_weighted_sum(old(buf), 0, 0) by {
    rewrite(adler_weighted_sum(old(buf), 0, 0), 0);
    close() using { to_integer(sum2) == 0; };
   }
   have to_integer(adler) <= 1 + 255 * to_integer(0) by close() using { to_integer(adler) == 1; };
   have to_integer(sum2) <= 1415761 * to_integer(0) by close() using { to_integer(sum2) == 0; };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), 0); close(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), 0); close(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), 0); close(); }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), 0); close(); }
   close();
  }
  maintain by {
   have 16u64 <= len by close();
   have len <= 5551u64 by close() using { len <= old(len); old(len) <= 5551u64; };
   have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
   have 1u64 <= len by close() using { 16u64 <= len; };
   have viewable(buf[0u64..16u64]) by close();
   apply(zlib_remaining_step(old(len), len, 16u64));
   have old(len) - len <= 22208u64 by close() using { old(len) - len <= 5551u64; };
   apply(zlib_prefix_observation(old(len), len));
   have old(len) - len < old(len) by close() using { 16u64 <= len; len <= old(len); old(len) <= 5551u64; };
   mark before_block;
   have forall (k: uint64) { k < at(before_block, len) implies at(before_block, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have k < len by close();
      instantiate(forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] }, k);
      close() using { load<uint8>(buf + k) == old(buf)[(old(len) - len) + k]; };
     }
    }
   }
   have 1u64 < len by close();
   instantiate(forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] }, 1u64);
   have at(before_block, load<uint8>(buf + 1u64)) == old(buf[(old(len) - at(before_block, len)) + 1u64]) by {
    close() using { load<uint8>(buf + 1u64) == old(buf)[(old(len) - len) + 1u64]; };
   }
   step();
   have len == at(before_block, len - 16u64) by close();
   have to_integer(len) == at(before_block, to_integer(len)) - 16 by close();
   step_until(assignment(adler, 22).entry);
   have 16 <= to_integer(at(before_block, len)) by close();
   have to_integer(old(len)) <= 5551 by close();
   apply(integer::uint64_subtract_to_integer(old(len), at(before_block, len)));
   have to_integer(old(len) - at(before_block, len)) <= 5535 by {
    rewrite(to_integer(old(len) - at(before_block, len)), to_integer(old(len)) - to_integer(at(before_block, len)));
    apply(integer::subtract_le(to_integer(old(len)), 5551, to_integer(at(before_block, len)), 16));
    close();
   }
   apply(zlib_block_read_bound(old(len), at(before_block, len), 0u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 0)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 0));
   have 0u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(0u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(before_block, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_block, len)) + k] }, 0u64);
   have buf[0] == at(before_block, load<uint8>(buf + 0u64)) by close();
   have buf[0] == old(buf)[(old(len) - at(before_block, len)) + 0u64] by close() using { at(before_block, load<uint8>(buf + 0u64)) == old(buf)[(old(len) - at(before_block, len)) + 0u64]; };
   have (old(len) - at(before_block, len)) == (old(len) - at(before_block, len)) + 0u64 by close();
   have buf[0] == old(buf)[(old(len) - at(before_block, len))] by {
    rewrite((old(len) - at(before_block, len)), (old(len) - at(before_block, len)) + 0u64);
    close();
   }
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   have old(buf)[(old(len) - at(before_block, len))] == old(buf)[zlib_prefix_count(old(len), at(before_block, len))] by {
    close() using { old(buf) + (old(len) - at(before_block, len)) == old(buf) + zlib_prefix_count(old(len), at(before_block, len)); };
   }
   have buf[0] == old(buf)[zlib_prefix_count(old(len), at(before_block, len))] by {
    rewrite(buf[0], old(buf)[(old(len) - at(before_block, len))]);
    close();
   }
   apply(zlib_native_component_step(old(buf), zlib_prefix_count(old(len), at(before_block, len)), adler, sum2, buf[0]));
   have viewable(buf[0u64..1u64]) by close();
   mark byte_0;
   have at(byte_0, &buf[1]) == at(before_block, buf + 1u64) by close();
   have at(byte_0, load<uint8>(at(byte_0, &buf[1]))) == at(before_block, load<uint8>(buf + 1u64)) by {
    rewrite(at(byte_0, &buf[1]), at(before_block, buf + 1u64));
    close();
   }
   step();
   step_until(statement(8).statement(0).statement(1).statement(1).entry);
   step();
   have separate(statement(8).statement(0).statement(1).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(1).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(1).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(1).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(1).statement(1));
      }
      have at(statement(8).statement(0).statement(1).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(before_block, load<uint8>(buf + k)) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(before_block, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(1).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(1).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(before_block, load<uint8>(buf + k));
       at(before_block, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have separate(statement(8).statement(0).statement(1).statement(1).footprint, at(byte_0, memory((&buf[1])[0..1]))) by close();
   have at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(byte_0, &buf[1]))) == at(statement(8).statement(0).statement(1).statement(1).entry, load<uint8>(at(byte_0, &buf[1]))) by {
    preserve(at(byte_0, memory((&buf[1])[0..1])), statement(8).statement(0).statement(1).statement(1));
   }
   have adler == at(byte_0, adler + buf[0] as uint32 as uint64) by close();
   have sum2 == at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1) by {
    rewrite(adler, at(byte_0, adler + buf[0] as uint32 as uint64));
    rewrite(at(byte_0, to_integer(adler) + to_integer(buf[0] as uint32 as uint64)), at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)));
    close() using { at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1); };
   }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1, zlib_prefix_count(old(len), at(before_block, len)) + 1) by {
    rewrite(sum2, at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)));
    rewrite(at(byte_0, to_integer(adler) + to_integer(buf[0] as uint32 as uint64)), at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)));
    rewrite(at(byte_0, to_integer(sum2) + to_integer(adler + buf[0] as uint32 as uint64)), at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))));
    close() using { at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_block, len)) + 1, zlib_prefix_count(old(len), at(before_block, len)) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) by {
    rewrite(adler, at(byte_0, adler + buf[0] as uint32 as uint64));
    rewrite(at(byte_0, to_integer(adler) + to_integer(buf[0] as uint32 as uint64)), at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)));
    close() using { at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1) by {
    rewrite(sum2, at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)));
    rewrite(at(byte_0, to_integer(adler) + to_integer(buf[0] as uint32 as uint64)), at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)));
    rewrite(at(byte_0, to_integer(sum2) + to_integer(adler + buf[0] as uint32 as uint64)), at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))));
    close() using { at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) <= 1415761 * to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 1); };
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1)) by close();
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1), (zlib_prefix_count(old(len), at(before_block, len)) + 1)) by close();
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) by close();
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1)) by close();
   step_until(assignment(adler, 23).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 1u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 1)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 1));
   have ((old(len) - at(before_block, len)) + 1u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 1u64));
   have to_integer((old(len) - at(before_block, len))) + 1 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 1, 1));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 1, 5535 + 1, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 1u64));
   have buf[1] == old(buf)[((old(len) - at(before_block, len)) + 1u64)] by {
    rewrite(buf, old(buf) + (old(len) - at(before_block, len)));
    close();
   }
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 1));
   have old(buf) + ((old(len) - at(before_block, len)) + 1u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 1) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 1u64), (old(buf) + (old(len) - at(before_block, len))) + 1u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 1u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 1] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 1u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 1); };
   }
   have buf[1] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 1] by {
    rewrite(buf[1], old(buf)[((old(len) - at(before_block, len)) + 1u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1), adler, sum2, buf[1]));
   mark byte_1;
   step();
   step_until(assignment(sum2, 23).entry);
   step();
   have separate(statement(8).statement(0).statement(3).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(3).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(3).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(3).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(3).statement(1));
      }
      have at(statement(8).statement(0).statement(3).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(3).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(3).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(1).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_1, adler + buf[1] as uint32 as uint64) by close();
   have sum2 == at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by {
    rewrite(adler, at(byte_1, adler + buf[1] as uint32 as uint64));
    rewrite(at(byte_1, to_integer(adler) + to_integer(buf[1] as uint32 as uint64)), at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)));
    close() using { at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by {
    rewrite(sum2, at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)));
    rewrite(at(byte_1, to_integer(adler) + to_integer(buf[1] as uint32 as uint64)), at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)));
    rewrite(at(byte_1, to_integer(sum2) + to_integer(adler + buf[1] as uint32 as uint64)), at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))));
    close() using { at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by {
    rewrite(adler, at(byte_1, adler + buf[1] as uint32 as uint64));
    rewrite(at(byte_1, to_integer(adler) + to_integer(buf[1] as uint32 as uint64)), at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)));
    close() using { at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by {
    rewrite(sum2, at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)));
    rewrite(at(byte_1, to_integer(adler) + to_integer(buf[1] as uint32 as uint64)), at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)));
    rewrite(at(byte_1, to_integer(sum2) + to_integer(adler + buf[1] as uint32 as uint64)), at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))));
    close() using { at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 2) == ((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 2), ((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2), (zlib_prefix_count(old(len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 2), ((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 2), ((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 2), ((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 1) + 1); };
   }
   step_until(assignment(adler, 24).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 2u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 2)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 2));
   have ((old(len) - at(before_block, len)) + 2u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 2u64));
   have to_integer((old(len) - at(before_block, len))) + 2 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 2, 2));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 2, 5535 + 2, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 2u64));
   have 2u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(2u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 2u64);
   have buf[2] == at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + 2u64))) by close();
   have buf[2] == old(buf)[((old(len) - at(before_block, len)) + 2u64)] by close() using {
    buf[2] == at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + 2u64)));
    at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + 2u64))) == old(buf)[(old(len) - at(before_block, len)) + 2u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 2));
   have old(buf) + ((old(len) - at(before_block, len)) + 2u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 2) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 2u64), (old(buf) + (old(len) - at(before_block, len))) + 2u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 2u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 2] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 2u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 2); };
   }
   have buf[2] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 2] by {
    rewrite(buf[2], old(buf)[((old(len) - at(before_block, len)) + 2u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2), adler, sum2, buf[2]));
   mark byte_2;
   step();
   step_until(assignment(sum2, 24).entry);
   step();
   have separate(statement(8).statement(0).statement(6).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(6).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(6).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(6).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(6).statement(1));
      }
      have at(statement(8).statement(0).statement(6).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(6).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(6).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(3).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_2, adler + buf[2] as uint32 as uint64) by close();
   have sum2 == at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by {
    rewrite(adler, at(byte_2, adler + buf[2] as uint32 as uint64));
    rewrite(at(byte_2, to_integer(adler) + to_integer(buf[2] as uint32 as uint64)), at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)));
    close() using { at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by {
    rewrite(sum2, at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)));
    rewrite(at(byte_2, to_integer(adler) + to_integer(buf[2] as uint32 as uint64)), at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)));
    rewrite(at(byte_2, to_integer(sum2) + to_integer(adler + buf[2] as uint32 as uint64)), at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))));
    close() using { at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by {
    rewrite(adler, at(byte_2, adler + buf[2] as uint32 as uint64));
    rewrite(at(byte_2, to_integer(adler) + to_integer(buf[2] as uint32 as uint64)), at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)));
    close() using { at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by {
    rewrite(sum2, at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)));
    rewrite(at(byte_2, to_integer(adler) + to_integer(buf[2] as uint32 as uint64)), at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)));
    rewrite(at(byte_2, to_integer(sum2) + to_integer(adler + buf[2] as uint32 as uint64)), at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))));
    close() using { at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 3) == ((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 3), ((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3), (zlib_prefix_count(old(len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 3), ((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 3), ((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 3), ((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 2) + 1); };
   }
   step_until(assignment(adler, 25).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 3u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 3)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 3));
   have ((old(len) - at(before_block, len)) + 3u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 3u64));
   have to_integer((old(len) - at(before_block, len))) + 3 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 3, 3));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 3, 5535 + 3, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 3u64));
   have 3u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(3u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 3u64);
   have buf[3] == at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + 3u64))) by close();
   have buf[3] == old(buf)[((old(len) - at(before_block, len)) + 3u64)] by close() using {
    buf[3] == at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + 3u64)));
    at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + 3u64))) == old(buf)[(old(len) - at(before_block, len)) + 3u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 3));
   have old(buf) + ((old(len) - at(before_block, len)) + 3u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 3) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 3u64), (old(buf) + (old(len) - at(before_block, len))) + 3u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 3u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 3] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 3u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 3); };
   }
   have buf[3] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 3] by {
    rewrite(buf[3], old(buf)[((old(len) - at(before_block, len)) + 3u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3), adler, sum2, buf[3]));
   mark byte_3;
   step();
   step_until(assignment(sum2, 25).entry);
   step();
   have separate(statement(8).statement(0).statement(8).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(8).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(8).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(8).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(8).statement(1));
      }
      have at(statement(8).statement(0).statement(8).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(8).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(8).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(6).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_3, adler + buf[3] as uint32 as uint64) by close();
   have sum2 == at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by {
    rewrite(adler, at(byte_3, adler + buf[3] as uint32 as uint64));
    rewrite(at(byte_3, to_integer(adler) + to_integer(buf[3] as uint32 as uint64)), at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)));
    close() using { at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by {
    rewrite(sum2, at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)));
    rewrite(at(byte_3, to_integer(adler) + to_integer(buf[3] as uint32 as uint64)), at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)));
    rewrite(at(byte_3, to_integer(sum2) + to_integer(adler + buf[3] as uint32 as uint64)), at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))));
    close() using { at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by {
    rewrite(adler, at(byte_3, adler + buf[3] as uint32 as uint64));
    rewrite(at(byte_3, to_integer(adler) + to_integer(buf[3] as uint32 as uint64)), at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)));
    close() using { at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by {
    rewrite(sum2, at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)));
    rewrite(at(byte_3, to_integer(adler) + to_integer(buf[3] as uint32 as uint64)), at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)));
    rewrite(at(byte_3, to_integer(sum2) + to_integer(adler + buf[3] as uint32 as uint64)), at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))));
    close() using { at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 4) == ((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 4), ((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4), (zlib_prefix_count(old(len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 4), ((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 4), ((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 4), ((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 3) + 1); };
   }
   step_until(assignment(adler, 26).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 4u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 4)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 4));
   have ((old(len) - at(before_block, len)) + 4u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 4u64));
   have to_integer((old(len) - at(before_block, len))) + 4 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 4, 4));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 4, 5535 + 4, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 4u64));
   have 4u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(4u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 4u64);
   have buf[4] == at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + 4u64))) by close();
   have buf[4] == old(buf)[((old(len) - at(before_block, len)) + 4u64)] by close() using {
    buf[4] == at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + 4u64)));
    at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + 4u64))) == old(buf)[(old(len) - at(before_block, len)) + 4u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 4));
   have old(buf) + ((old(len) - at(before_block, len)) + 4u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 4) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 4u64), (old(buf) + (old(len) - at(before_block, len))) + 4u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 4u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 4] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 4u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 4); };
   }
   have buf[4] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 4] by {
    rewrite(buf[4], old(buf)[((old(len) - at(before_block, len)) + 4u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4), adler, sum2, buf[4]));
   mark byte_4;
   step();
   step_until(assignment(sum2, 26).entry);
   step();
   have separate(statement(8).statement(0).statement(12).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(12).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(12).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(12).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(12).statement(1));
      }
      have at(statement(8).statement(0).statement(12).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(12).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(12).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(8).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_4, adler + buf[4] as uint32 as uint64) by close();
   have sum2 == at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by {
    rewrite(adler, at(byte_4, adler + buf[4] as uint32 as uint64));
    rewrite(at(byte_4, to_integer(adler) + to_integer(buf[4] as uint32 as uint64)), at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)));
    close() using { at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by {
    rewrite(sum2, at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)));
    rewrite(at(byte_4, to_integer(adler) + to_integer(buf[4] as uint32 as uint64)), at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)));
    rewrite(at(byte_4, to_integer(sum2) + to_integer(adler + buf[4] as uint32 as uint64)), at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))));
    close() using { at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by {
    rewrite(adler, at(byte_4, adler + buf[4] as uint32 as uint64));
    rewrite(at(byte_4, to_integer(adler) + to_integer(buf[4] as uint32 as uint64)), at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)));
    close() using { at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by {
    rewrite(sum2, at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)));
    rewrite(at(byte_4, to_integer(adler) + to_integer(buf[4] as uint32 as uint64)), at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)));
    rewrite(at(byte_4, to_integer(sum2) + to_integer(adler + buf[4] as uint32 as uint64)), at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))));
    close() using { at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 5) == ((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 5), ((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5), (zlib_prefix_count(old(len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 5), ((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 5), ((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 5), ((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 4) + 1); };
   }
   step_until(assignment(adler, 27).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 5u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 5)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 5));
   have ((old(len) - at(before_block, len)) + 5u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 5u64));
   have to_integer((old(len) - at(before_block, len))) + 5 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 5, 5));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 5, 5535 + 5, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 5u64));
   have 5u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(5u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 5u64);
   have buf[5] == at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + 5u64))) by close();
   have buf[5] == old(buf)[((old(len) - at(before_block, len)) + 5u64)] by close() using {
    buf[5] == at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + 5u64)));
    at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + 5u64))) == old(buf)[(old(len) - at(before_block, len)) + 5u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 5));
   have old(buf) + ((old(len) - at(before_block, len)) + 5u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 5) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 5u64), (old(buf) + (old(len) - at(before_block, len))) + 5u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 5u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 5] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 5u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 5); };
   }
   have buf[5] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 5] by {
    rewrite(buf[5], old(buf)[((old(len) - at(before_block, len)) + 5u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5), adler, sum2, buf[5]));
   mark byte_5;
   step();
   step_until(assignment(sum2, 27).entry);
   step();
   have separate(statement(8).statement(0).statement(14).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(14).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(14).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(14).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(14).statement(1));
      }
      have at(statement(8).statement(0).statement(14).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(14).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(14).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(12).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_5, adler + buf[5] as uint32 as uint64) by close();
   have sum2 == at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by {
    rewrite(adler, at(byte_5, adler + buf[5] as uint32 as uint64));
    rewrite(at(byte_5, to_integer(adler) + to_integer(buf[5] as uint32 as uint64)), at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)));
    close() using { at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by {
    rewrite(sum2, at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)));
    rewrite(at(byte_5, to_integer(adler) + to_integer(buf[5] as uint32 as uint64)), at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)));
    rewrite(at(byte_5, to_integer(sum2) + to_integer(adler + buf[5] as uint32 as uint64)), at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))));
    close() using { at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by {
    rewrite(adler, at(byte_5, adler + buf[5] as uint32 as uint64));
    rewrite(at(byte_5, to_integer(adler) + to_integer(buf[5] as uint32 as uint64)), at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)));
    close() using { at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by {
    rewrite(sum2, at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)));
    rewrite(at(byte_5, to_integer(adler) + to_integer(buf[5] as uint32 as uint64)), at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)));
    rewrite(at(byte_5, to_integer(sum2) + to_integer(adler + buf[5] as uint32 as uint64)), at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))));
    close() using { at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 6) == ((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 6), ((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6), (zlib_prefix_count(old(len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 6), ((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 6), ((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 6), ((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 5) + 1); };
   }
   step_until(assignment(adler, 28).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 6u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 6)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 6));
   have ((old(len) - at(before_block, len)) + 6u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 6u64));
   have to_integer((old(len) - at(before_block, len))) + 6 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 6, 6));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 6, 5535 + 6, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 6u64));
   have 6u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(6u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 6u64);
   have buf[6] == at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + 6u64))) by close();
   have buf[6] == old(buf)[((old(len) - at(before_block, len)) + 6u64)] by close() using {
    buf[6] == at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + 6u64)));
    at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + 6u64))) == old(buf)[(old(len) - at(before_block, len)) + 6u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 6));
   have old(buf) + ((old(len) - at(before_block, len)) + 6u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 6) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 6u64), (old(buf) + (old(len) - at(before_block, len))) + 6u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 6u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 6] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 6u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 6); };
   }
   have buf[6] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 6] by {
    rewrite(buf[6], old(buf)[((old(len) - at(before_block, len)) + 6u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6), adler, sum2, buf[6]));
   mark byte_6;
   step();
   step_until(assignment(sum2, 28).entry);
   step();
   have separate(statement(8).statement(0).statement(17).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(17).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(17).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(17).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(17).statement(1));
      }
      have at(statement(8).statement(0).statement(17).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(17).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(17).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(14).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_6, adler + buf[6] as uint32 as uint64) by close();
   have sum2 == at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by {
    rewrite(adler, at(byte_6, adler + buf[6] as uint32 as uint64));
    rewrite(at(byte_6, to_integer(adler) + to_integer(buf[6] as uint32 as uint64)), at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)));
    close() using { at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by {
    rewrite(sum2, at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)));
    rewrite(at(byte_6, to_integer(adler) + to_integer(buf[6] as uint32 as uint64)), at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)));
    rewrite(at(byte_6, to_integer(sum2) + to_integer(adler + buf[6] as uint32 as uint64)), at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))));
    close() using { at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by {
    rewrite(adler, at(byte_6, adler + buf[6] as uint32 as uint64));
    rewrite(at(byte_6, to_integer(adler) + to_integer(buf[6] as uint32 as uint64)), at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)));
    close() using { at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by {
    rewrite(sum2, at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)));
    rewrite(at(byte_6, to_integer(adler) + to_integer(buf[6] as uint32 as uint64)), at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)));
    rewrite(at(byte_6, to_integer(sum2) + to_integer(adler + buf[6] as uint32 as uint64)), at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))));
    close() using { at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 7) == ((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 7), ((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7), (zlib_prefix_count(old(len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 7), ((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 7), ((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 7), ((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 6) + 1); };
   }
   step_until(assignment(adler, 29).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 7u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 7)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 7));
   have ((old(len) - at(before_block, len)) + 7u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 7u64));
   have to_integer((old(len) - at(before_block, len))) + 7 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 7, 7));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 7, 5535 + 7, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 7u64));
   have 7u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(7u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 7u64);
   have buf[7] == at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + 7u64))) by close();
   have buf[7] == old(buf)[((old(len) - at(before_block, len)) + 7u64)] by close() using {
    buf[7] == at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + 7u64)));
    at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + 7u64))) == old(buf)[(old(len) - at(before_block, len)) + 7u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 7));
   have old(buf) + ((old(len) - at(before_block, len)) + 7u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 7) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 7u64), (old(buf) + (old(len) - at(before_block, len))) + 7u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 7u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 7] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 7u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 7); };
   }
   have buf[7] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 7] by {
    rewrite(buf[7], old(buf)[((old(len) - at(before_block, len)) + 7u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7), adler, sum2, buf[7]));
   mark byte_7;
   step();
   step_until(assignment(sum2, 29).entry);
   step();
   have separate(statement(8).statement(0).statement(19).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(19).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(19).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(19).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(19).statement(1));
      }
      have at(statement(8).statement(0).statement(19).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(19).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(19).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(17).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_7, adler + buf[7] as uint32 as uint64) by close();
   have sum2 == at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by {
    rewrite(adler, at(byte_7, adler + buf[7] as uint32 as uint64));
    rewrite(at(byte_7, to_integer(adler) + to_integer(buf[7] as uint32 as uint64)), at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)));
    close() using { at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by {
    rewrite(sum2, at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)));
    rewrite(at(byte_7, to_integer(adler) + to_integer(buf[7] as uint32 as uint64)), at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)));
    rewrite(at(byte_7, to_integer(sum2) + to_integer(adler + buf[7] as uint32 as uint64)), at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))));
    close() using { at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by {
    rewrite(adler, at(byte_7, adler + buf[7] as uint32 as uint64));
    rewrite(at(byte_7, to_integer(adler) + to_integer(buf[7] as uint32 as uint64)), at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)));
    close() using { at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by {
    rewrite(sum2, at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)));
    rewrite(at(byte_7, to_integer(adler) + to_integer(buf[7] as uint32 as uint64)), at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)));
    rewrite(at(byte_7, to_integer(sum2) + to_integer(adler + buf[7] as uint32 as uint64)), at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))));
    close() using { at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 8) == ((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 8), ((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8), (zlib_prefix_count(old(len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 8), ((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 8), ((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 8), ((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 7) + 1); };
   }
   step_until(assignment(adler, 30).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 8u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 8)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 8));
   have ((old(len) - at(before_block, len)) + 8u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 8u64));
   have to_integer((old(len) - at(before_block, len))) + 8 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 8, 8));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 8, 5535 + 8, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 8u64));
   have 8u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(8u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 8u64);
   have buf[8] == at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + 8u64))) by close();
   have buf[8] == old(buf)[((old(len) - at(before_block, len)) + 8u64)] by close() using {
    buf[8] == at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + 8u64)));
    at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + 8u64))) == old(buf)[(old(len) - at(before_block, len)) + 8u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 8));
   have old(buf) + ((old(len) - at(before_block, len)) + 8u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 8) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 8u64), (old(buf) + (old(len) - at(before_block, len))) + 8u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 8u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 8] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 8u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 8); };
   }
   have buf[8] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 8] by {
    rewrite(buf[8], old(buf)[((old(len) - at(before_block, len)) + 8u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8), adler, sum2, buf[8]));
   mark byte_8;
   step();
   step_until(assignment(sum2, 30).entry);
   step();
   have separate(statement(8).statement(0).statement(24).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(24).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(24).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(24).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(24).statement(1));
      }
      have at(statement(8).statement(0).statement(24).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(24).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(24).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(19).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_8, adler + buf[8] as uint32 as uint64) by close();
   have sum2 == at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by {
    rewrite(adler, at(byte_8, adler + buf[8] as uint32 as uint64));
    rewrite(at(byte_8, to_integer(adler) + to_integer(buf[8] as uint32 as uint64)), at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)));
    close() using { at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by {
    rewrite(sum2, at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)));
    rewrite(at(byte_8, to_integer(adler) + to_integer(buf[8] as uint32 as uint64)), at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)));
    rewrite(at(byte_8, to_integer(sum2) + to_integer(adler + buf[8] as uint32 as uint64)), at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))));
    close() using { at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by {
    rewrite(adler, at(byte_8, adler + buf[8] as uint32 as uint64));
    rewrite(at(byte_8, to_integer(adler) + to_integer(buf[8] as uint32 as uint64)), at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)));
    close() using { at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by {
    rewrite(sum2, at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)));
    rewrite(at(byte_8, to_integer(adler) + to_integer(buf[8] as uint32 as uint64)), at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)));
    rewrite(at(byte_8, to_integer(sum2) + to_integer(adler + buf[8] as uint32 as uint64)), at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))));
    close() using { at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 9) == ((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 9), ((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9), (zlib_prefix_count(old(len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 9), ((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 9), ((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 9), ((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 8) + 1); };
   }
   step_until(assignment(adler, 31).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 9u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 9)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 9));
   have ((old(len) - at(before_block, len)) + 9u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 9u64));
   have to_integer((old(len) - at(before_block, len))) + 9 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 9, 9));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 9, 5535 + 9, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 9u64));
   have 9u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(9u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 9u64);
   have buf[9] == at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + 9u64))) by close();
   have buf[9] == old(buf)[((old(len) - at(before_block, len)) + 9u64)] by close() using {
    buf[9] == at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + 9u64)));
    at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + 9u64))) == old(buf)[(old(len) - at(before_block, len)) + 9u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 9));
   have old(buf) + ((old(len) - at(before_block, len)) + 9u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 9) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 9u64), (old(buf) + (old(len) - at(before_block, len))) + 9u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 9u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 9] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 9u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 9); };
   }
   have buf[9] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 9] by {
    rewrite(buf[9], old(buf)[((old(len) - at(before_block, len)) + 9u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9), adler, sum2, buf[9]));
   mark byte_9;
   step();
   step_until(assignment(sum2, 31).entry);
   step();
   have separate(statement(8).statement(0).statement(26).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(26).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(26).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(26).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(26).statement(1));
      }
      have at(statement(8).statement(0).statement(26).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(26).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(26).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(24).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_9, adler + buf[9] as uint32 as uint64) by close();
   have sum2 == at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by {
    rewrite(adler, at(byte_9, adler + buf[9] as uint32 as uint64));
    rewrite(at(byte_9, to_integer(adler) + to_integer(buf[9] as uint32 as uint64)), at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)));
    close() using { at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by {
    rewrite(sum2, at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)));
    rewrite(at(byte_9, to_integer(adler) + to_integer(buf[9] as uint32 as uint64)), at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)));
    rewrite(at(byte_9, to_integer(sum2) + to_integer(adler + buf[9] as uint32 as uint64)), at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))));
    close() using { at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by {
    rewrite(adler, at(byte_9, adler + buf[9] as uint32 as uint64));
    rewrite(at(byte_9, to_integer(adler) + to_integer(buf[9] as uint32 as uint64)), at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)));
    close() using { at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by {
    rewrite(sum2, at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)));
    rewrite(at(byte_9, to_integer(adler) + to_integer(buf[9] as uint32 as uint64)), at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)));
    rewrite(at(byte_9, to_integer(sum2) + to_integer(adler + buf[9] as uint32 as uint64)), at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))));
    close() using { at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 10) == ((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 10), ((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10), (zlib_prefix_count(old(len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 10), ((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 10), ((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 10), ((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 9) + 1); };
   }
   step_until(assignment(adler, 32).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 10u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 10)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 10));
   have ((old(len) - at(before_block, len)) + 10u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 10u64));
   have to_integer((old(len) - at(before_block, len))) + 10 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 10, 10));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 10, 5535 + 10, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 10u64));
   have 10u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(10u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 10u64);
   have buf[10] == at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + 10u64))) by close();
   have buf[10] == old(buf)[((old(len) - at(before_block, len)) + 10u64)] by close() using {
    buf[10] == at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + 10u64)));
    at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + 10u64))) == old(buf)[(old(len) - at(before_block, len)) + 10u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 10));
   have old(buf) + ((old(len) - at(before_block, len)) + 10u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 10) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 10u64), (old(buf) + (old(len) - at(before_block, len))) + 10u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 10u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 10] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 10u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 10); };
   }
   have buf[10] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 10] by {
    rewrite(buf[10], old(buf)[((old(len) - at(before_block, len)) + 10u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10), adler, sum2, buf[10]));
   mark byte_10;
   step();
   step_until(assignment(sum2, 32).entry);
   step();
   have separate(statement(8).statement(0).statement(29).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(29).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(29).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(29).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(29).statement(1));
      }
      have at(statement(8).statement(0).statement(29).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(29).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(29).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(26).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_10, adler + buf[10] as uint32 as uint64) by close();
   have sum2 == at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by {
    rewrite(adler, at(byte_10, adler + buf[10] as uint32 as uint64));
    rewrite(at(byte_10, to_integer(adler) + to_integer(buf[10] as uint32 as uint64)), at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)));
    close() using { at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by {
    rewrite(sum2, at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)));
    rewrite(at(byte_10, to_integer(adler) + to_integer(buf[10] as uint32 as uint64)), at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)));
    rewrite(at(byte_10, to_integer(sum2) + to_integer(adler + buf[10] as uint32 as uint64)), at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))));
    close() using { at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by {
    rewrite(adler, at(byte_10, adler + buf[10] as uint32 as uint64));
    rewrite(at(byte_10, to_integer(adler) + to_integer(buf[10] as uint32 as uint64)), at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)));
    close() using { at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by {
    rewrite(sum2, at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)));
    rewrite(at(byte_10, to_integer(adler) + to_integer(buf[10] as uint32 as uint64)), at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)));
    rewrite(at(byte_10, to_integer(sum2) + to_integer(adler + buf[10] as uint32 as uint64)), at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))));
    close() using { at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 11) == ((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 11), ((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11), (zlib_prefix_count(old(len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 11), ((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 11), ((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 11), ((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 10) + 1); };
   }
   step_until(assignment(adler, 33).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 11u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 11)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 11));
   have ((old(len) - at(before_block, len)) + 11u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 11u64));
   have to_integer((old(len) - at(before_block, len))) + 11 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 11, 11));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 11, 5535 + 11, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 11u64));
   have 11u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(11u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 11u64);
   have buf[11] == at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + 11u64))) by close();
   have buf[11] == old(buf)[((old(len) - at(before_block, len)) + 11u64)] by close() using {
    buf[11] == at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + 11u64)));
    at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + 11u64))) == old(buf)[(old(len) - at(before_block, len)) + 11u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 11));
   have old(buf) + ((old(len) - at(before_block, len)) + 11u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 11) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 11u64), (old(buf) + (old(len) - at(before_block, len))) + 11u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 11u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 11] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 11u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 11); };
   }
   have buf[11] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 11] by {
    rewrite(buf[11], old(buf)[((old(len) - at(before_block, len)) + 11u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11), adler, sum2, buf[11]));
   mark byte_11;
   step();
   step_until(assignment(sum2, 33).entry);
   step();
   have separate(statement(8).statement(0).statement(31).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(31).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(31).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(31).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(31).statement(1));
      }
      have at(statement(8).statement(0).statement(31).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(31).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(31).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(29).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_11, adler + buf[11] as uint32 as uint64) by close();
   have sum2 == at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by {
    rewrite(adler, at(byte_11, adler + buf[11] as uint32 as uint64));
    rewrite(at(byte_11, to_integer(adler) + to_integer(buf[11] as uint32 as uint64)), at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)));
    close() using { at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by {
    rewrite(sum2, at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)));
    rewrite(at(byte_11, to_integer(adler) + to_integer(buf[11] as uint32 as uint64)), at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)));
    rewrite(at(byte_11, to_integer(sum2) + to_integer(adler + buf[11] as uint32 as uint64)), at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))));
    close() using { at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by {
    rewrite(adler, at(byte_11, adler + buf[11] as uint32 as uint64));
    rewrite(at(byte_11, to_integer(adler) + to_integer(buf[11] as uint32 as uint64)), at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)));
    close() using { at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by {
    rewrite(sum2, at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)));
    rewrite(at(byte_11, to_integer(adler) + to_integer(buf[11] as uint32 as uint64)), at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)));
    rewrite(at(byte_11, to_integer(sum2) + to_integer(adler + buf[11] as uint32 as uint64)), at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))));
    close() using { at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 12) == ((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 12), ((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12), (zlib_prefix_count(old(len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 12), ((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 12), ((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 12), ((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 11) + 1); };
   }
   step_until(assignment(adler, 34).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 12u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 12)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 12));
   have ((old(len) - at(before_block, len)) + 12u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 12u64));
   have to_integer((old(len) - at(before_block, len))) + 12 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 12, 12));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 12, 5535 + 12, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 12u64));
   have 12u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(12u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 12u64);
   have buf[12] == at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + 12u64))) by close();
   have buf[12] == old(buf)[((old(len) - at(before_block, len)) + 12u64)] by close() using {
    buf[12] == at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + 12u64)));
    at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + 12u64))) == old(buf)[(old(len) - at(before_block, len)) + 12u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 12));
   have old(buf) + ((old(len) - at(before_block, len)) + 12u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 12) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 12u64), (old(buf) + (old(len) - at(before_block, len))) + 12u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 12u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 12] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 12u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 12); };
   }
   have buf[12] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 12] by {
    rewrite(buf[12], old(buf)[((old(len) - at(before_block, len)) + 12u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12), adler, sum2, buf[12]));
   mark byte_12;
   step();
   step_until(assignment(sum2, 34).entry);
   step();
   have separate(statement(8).statement(0).statement(35).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(35).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(35).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(35).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(35).statement(1));
      }
      have at(statement(8).statement(0).statement(35).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(35).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(35).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(31).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_12, adler + buf[12] as uint32 as uint64) by close();
   have sum2 == at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by {
    rewrite(adler, at(byte_12, adler + buf[12] as uint32 as uint64));
    rewrite(at(byte_12, to_integer(adler) + to_integer(buf[12] as uint32 as uint64)), at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)));
    close() using { at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by {
    rewrite(sum2, at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)));
    rewrite(at(byte_12, to_integer(adler) + to_integer(buf[12] as uint32 as uint64)), at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)));
    rewrite(at(byte_12, to_integer(sum2) + to_integer(adler + buf[12] as uint32 as uint64)), at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))));
    close() using { at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by {
    rewrite(adler, at(byte_12, adler + buf[12] as uint32 as uint64));
    rewrite(at(byte_12, to_integer(adler) + to_integer(buf[12] as uint32 as uint64)), at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)));
    close() using { at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by {
    rewrite(sum2, at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)));
    rewrite(at(byte_12, to_integer(adler) + to_integer(buf[12] as uint32 as uint64)), at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)));
    rewrite(at(byte_12, to_integer(sum2) + to_integer(adler + buf[12] as uint32 as uint64)), at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))));
    close() using { at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 13) == ((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 13), ((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13), (zlib_prefix_count(old(len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 13), ((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 13), ((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 13), ((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 12) + 1); };
   }
   step_until(assignment(adler, 35).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 13u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 13)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 13));
   have ((old(len) - at(before_block, len)) + 13u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 13u64));
   have to_integer((old(len) - at(before_block, len))) + 13 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 13, 13));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 13, 5535 + 13, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 13u64));
   have 13u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(13u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 13u64);
   have buf[13] == at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + 13u64))) by close();
   have buf[13] == old(buf)[((old(len) - at(before_block, len)) + 13u64)] by close() using {
    buf[13] == at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + 13u64)));
    at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + 13u64))) == old(buf)[(old(len) - at(before_block, len)) + 13u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 13));
   have old(buf) + ((old(len) - at(before_block, len)) + 13u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 13) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 13u64), (old(buf) + (old(len) - at(before_block, len))) + 13u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 13u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 13] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 13u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 13); };
   }
   have buf[13] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 13] by {
    rewrite(buf[13], old(buf)[((old(len) - at(before_block, len)) + 13u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13), adler, sum2, buf[13]));
   mark byte_13;
   step();
   step_until(assignment(sum2, 35).entry);
   step();
   have separate(statement(8).statement(0).statement(37).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(37).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(37).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(37).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(37).statement(1));
      }
      have at(statement(8).statement(0).statement(37).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(37).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(37).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(35).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_13, adler + buf[13] as uint32 as uint64) by close();
   have sum2 == at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by {
    rewrite(adler, at(byte_13, adler + buf[13] as uint32 as uint64));
    rewrite(at(byte_13, to_integer(adler) + to_integer(buf[13] as uint32 as uint64)), at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)));
    close() using { at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by {
    rewrite(sum2, at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)));
    rewrite(at(byte_13, to_integer(adler) + to_integer(buf[13] as uint32 as uint64)), at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)));
    rewrite(at(byte_13, to_integer(sum2) + to_integer(adler + buf[13] as uint32 as uint64)), at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))));
    close() using { at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by {
    rewrite(adler, at(byte_13, adler + buf[13] as uint32 as uint64));
    rewrite(at(byte_13, to_integer(adler) + to_integer(buf[13] as uint32 as uint64)), at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)));
    close() using { at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by {
    rewrite(sum2, at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)));
    rewrite(at(byte_13, to_integer(adler) + to_integer(buf[13] as uint32 as uint64)), at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)));
    rewrite(at(byte_13, to_integer(sum2) + to_integer(adler + buf[13] as uint32 as uint64)), at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))));
    close() using { at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 14) == ((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 14), ((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14), (zlib_prefix_count(old(len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 14), ((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 14), ((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 14), ((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 13) + 1); };
   }
   step_until(assignment(adler, 36).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 14u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 14)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 14));
   have ((old(len) - at(before_block, len)) + 14u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 14u64));
   have to_integer((old(len) - at(before_block, len))) + 14 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 14, 14));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 14, 5535 + 14, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 14u64));
   have 14u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(14u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 14u64);
   have buf[14] == at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + 14u64))) by close();
   have buf[14] == old(buf)[((old(len) - at(before_block, len)) + 14u64)] by close() using {
    buf[14] == at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + 14u64)));
    at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + 14u64))) == old(buf)[(old(len) - at(before_block, len)) + 14u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 14));
   have old(buf) + ((old(len) - at(before_block, len)) + 14u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 14) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 14u64), (old(buf) + (old(len) - at(before_block, len))) + 14u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 14u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 14] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 14u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 14); };
   }
   have buf[14] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 14] by {
    rewrite(buf[14], old(buf)[((old(len) - at(before_block, len)) + 14u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14), adler, sum2, buf[14]));
   mark byte_14;
   step();
   step_until(assignment(sum2, 36).entry);
   step();
   have separate(statement(8).statement(0).statement(40).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(40).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(40).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(40).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(40).statement(1));
      }
      have at(statement(8).statement(0).statement(40).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(40).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(40).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(37).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_14, adler + buf[14] as uint32 as uint64) by close();
   have sum2 == at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by {
    rewrite(adler, at(byte_14, adler + buf[14] as uint32 as uint64));
    rewrite(at(byte_14, to_integer(adler) + to_integer(buf[14] as uint32 as uint64)), at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)));
    close() using { at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by {
    rewrite(sum2, at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)));
    rewrite(at(byte_14, to_integer(adler) + to_integer(buf[14] as uint32 as uint64)), at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)));
    rewrite(at(byte_14, to_integer(sum2) + to_integer(adler + buf[14] as uint32 as uint64)), at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))));
    close() using { at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by {
    rewrite(adler, at(byte_14, adler + buf[14] as uint32 as uint64));
    rewrite(at(byte_14, to_integer(adler) + to_integer(buf[14] as uint32 as uint64)), at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)));
    close() using { at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by {
    rewrite(sum2, at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)));
    rewrite(at(byte_14, to_integer(adler) + to_integer(buf[14] as uint32 as uint64)), at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)));
    rewrite(at(byte_14, to_integer(sum2) + to_integer(adler + buf[14] as uint32 as uint64)), at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))));
    close() using { at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 15) == ((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 15), ((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15), (zlib_prefix_count(old(len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 15), ((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 15), ((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 15), ((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 14) + 1); };
   }
   step_until(assignment(adler, 37).entry);
   apply(zlib_block_read_bound(old(len), at(before_block, len), 15u64));
   apply(zlib_block_lane_defined(old(buf), old(len), at(before_block, len), 15)); apply(zlib_block_lane(old(buf), old(len), at(before_block, len), 15));
   have ((old(len) - at(before_block, len)) + 15u64) < old(len) by close() using { 16 <= to_integer(at(before_block, len)); };
   instantiate(forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) }, ((old(len) - at(before_block, len)) + 15u64));
   have to_integer((old(len) - at(before_block, len))) + 15 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer((old(len) - at(before_block, len))), 5535, 15, 15));
    apply(integer::le_transitive(to_integer((old(len) - at(before_block, len))) + 15, 5535 + 15, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), (old(len) - at(before_block, len)), 15u64));
   have 15u64 < at(before_block, len) by {
    apply(integer::uint64_less_than_less_equal_transitive(15u64, 16u64, at(before_block, len)));
   }
   instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 15u64);
   have buf[15] == at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + 15u64))) by close();
   have buf[15] == old(buf)[((old(len) - at(before_block, len)) + 15u64)] by close() using {
    buf[15] == at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + 15u64)));
    at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + 15u64))) == old(buf)[(old(len) - at(before_block, len)) + 15u64];
   };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_block, len)));
   apply(integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_block, len)), 15));
   have old(buf) + ((old(len) - at(before_block, len)) + 15u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 15) by {
    rewrite(old(buf) + ((old(len) - at(before_block, len)) + 15u64), (old(buf) + (old(len) - at(before_block, len))) + 15u64);
    rewrite(old(buf) + (old(len) - at(before_block, len)), old(buf) + zlib_prefix_count(old(len), at(before_block, len)));
    close();
   }
   have old(buf)[((old(len) - at(before_block, len)) + 15u64)] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 15] by {
    close() using { old(buf) + ((old(len) - at(before_block, len)) + 15u64) == old(buf) + (zlib_prefix_count(old(len), at(before_block, len)) + 15); };
   }
   have buf[15] == old(buf)[zlib_prefix_count(old(len), at(before_block, len)) + 15] by {
    rewrite(buf[15], old(buf)[((old(len) - at(before_block, len)) + 15u64)]);
    close();
   }
   apply(zlib_native_component_step(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15), adler, sum2, buf[15]));
   mark byte_15;
   step();
   step_until(assignment(sum2, 37).entry);
   step();
   have separate(statement(8).statement(0).statement(42).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(42).statement(1));
   }
   have forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(0).statement(42).statement(1).footprint, at(before_block, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(42).statement(1).entry, load<uint8>(at(before_block, buf + k))) by {
       preserve(at(before_block, memory((buf + k)[0..1])), statement(8).statement(0).statement(42).statement(1));
      }
      have at(statement(8).statement(0).statement(42).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) by close();
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, k);
      close() using {
       at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(42).statement(1).entry, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(42).statement(1).entry, load<uint8>(at(before_block, buf + k))) == at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k)));
       at(statement(8).statement(0).statement(40).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k];
      };
     }
    }
   }
   have adler == at(byte_15, adler + buf[15] as uint32 as uint64) by close();
   have sum2 == at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)) by close();
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by {
    rewrite(adler, at(byte_15, adler + buf[15] as uint32 as uint64));
    rewrite(at(byte_15, to_integer(adler) + to_integer(buf[15] as uint32 as uint64)), at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)));
    close() using { at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by {
    rewrite(sum2, at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)));
    rewrite(at(byte_15, to_integer(adler) + to_integer(buf[15] as uint32 as uint64)), at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)));
    rewrite(at(byte_15, to_integer(sum2) + to_integer(adler + buf[15] as uint32 as uint64)), at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))));
    close() using { at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by {
    rewrite(adler, at(byte_15, adler + buf[15] as uint32 as uint64));
    rewrite(at(byte_15, to_integer(adler) + to_integer(buf[15] as uint32 as uint64)), at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)));
    close() using { at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by {
    rewrite(sum2, at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)));
    rewrite(at(byte_15, to_integer(adler) + to_integer(buf[15] as uint32 as uint64)), at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)));
    rewrite(at(byte_15, to_integer(sum2) + to_integer(adler + buf[15] as uint32 as uint64)), at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))));
    close() using { at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have (zlib_prefix_count(old(len), at(before_block, len)) + 16) == ((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) by close() using {
    0 <= zlib_prefix_count(old(len), at(before_block, len)); zlib_prefix_count(old(len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 16), ((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 16), (zlib_prefix_count(old(len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 16), ((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(sum2) == to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1) + adler_weighted_sum(old(buf), (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 16), ((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(adler) <= 1 + 255 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(old(len), at(before_block, len)) + 16), ((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(sum2) <= 1415761 * to_integer((zlib_prefix_count(old(len), at(before_block, len)) + 15) + 1); };
   }
   step_until(loop.back_edge);
   have len <= old(len) by close();
   have 0 <= to_integer(len);
   have old(len) - len <= 5551u64 by {
    apply(integer::subtract_le(to_integer(old(len)), 5551, to_integer(len), 0));
    close();
   }
   have to_integer(len) <= 5551 by close() using { to_integer(len) == at(before_block, to_integer(len)) - 16; at(before_block, to_integer(len)) <= 5551; };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have len <= 5551u64;
   have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
   have to_integer(len) < at(before_block, to_integer(len)) by close() using { to_integer(len) == at(before_block, to_integer(len)) - 16; };
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + 16 by close();
   have -2147483648 <= to_integer(zlib_prefix_count(old(len), len)); have to_integer(zlib_prefix_count(old(len), len)) <= 2147483647;
   have -2147483648 <= to_integer(zlib_prefix_count(old(len), at(before_block, len))); have to_integer(zlib_prefix_count(old(len), at(before_block, len))) <= 2147483647;
   have to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16) >= -2147483648 by close() using { -2147483648 <= to_integer(zlib_prefix_count(old(len), at(before_block, len))); };
   have to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16) <= 2147483647 by {
    apply(integer::add_le(to_integer(zlib_prefix_count(old(len), at(before_block, len))), 22208, 16, 16));
    apply(integer::le_transitive(to_integer(zlib_prefix_count(old(len), at(before_block, len))) + 16, 22224, 2147483647));
   }
   have defined(zlib_prefix_count(old(len), at(before_block, len)) + 16);
   have defined(zlib_prefix_count(old(len), at(before_block, len)) + 16) by close();
   have to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16) == to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16);
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16) by {
    rewrite(to_integer(zlib_prefix_count(old(len), at(before_block, len)) + 16), to_integer(zlib_prefix_count(old(len), at(before_block, len))) + to_integer(16));
    close();
   }
   have buf == at(before_block, buf) + 16 by close();
   have old(len) - len == (old(len) - at(before_block, len)) + 16u64 by close() using {
    len == at(before_block, len - 16u64);
    16u64 <= at(before_block, len);
    at(before_block, len) <= old(len);
    old(len) <= 5551u64;
   };
   have to_integer(old(len) - at(before_block, len)) + 16 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer(old(len) - at(before_block, len)), 5535, 16, 16));
    apply(integer::le_transitive(to_integer(old(len) - at(before_block, len)) + 16, 5535 + 16, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), old(len) - at(before_block, len), 16u64));
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf, at(before_block, buf) + 16);
    rewrite(at(before_block, buf), old(buf) + (old(len) - at(before_block, len)));
    rewrite(old(len) - len, (old(len) - at(before_block, len)) + 16u64);
    close();
   }
   have len <= at(before_block, len) - 16u64 by close();
   apply(click::separation::contains_subrange(at(before_block, buf), 0u64, at(before_block, len), 16u64, at(before_block, len)));
   apply(click::separation::contains_rebase(at(before_block, buf), 16u64, at(before_block, len)));
   have contains(memory(at(before_block, buf)[16u64..at(before_block, len)]), memory(buf[0u64..len])) by {
    rewrite(buf, at(before_block, buf) + 16);
    rewrite(len, at(before_block, len - 16u64));
    apply(click::separation::contains_rebase(at(before_block, buf), 16u64, at(before_block, len)));
   }
   apply(click::separation::contains_trans(at(before_block, memory(buf[0u64..len])), memory(at(before_block, buf)[16u64..at(before_block, len)]), memory(buf[0u64..len])));
   apply(click::separation::viewable_restrict(at(before_block, memory(buf[0u64..len])), memory(buf[0u64..len])));
   have forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] } by {
    intro() {
     intro() {
      have to_integer(k) <= 5551 by close() using { k < len; to_integer(len) <= 5551; };
      have 16 + to_integer(k) <= 18446744073709551615 by close() using { to_integer(k) <= 5551; };
      apply(integer::uint64_add_to_integer(16u64, k));
      have 16u64 + k < at(before_block, len) by close() using {
       k < len;
       to_integer(len) == at(before_block, to_integer(len)) - 16;
       to_integer(16u64 + k) == to_integer(16u64) + to_integer(k);
      };
      instantiate(forall (k: uint64) { k < at(before_block, len) implies at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + k))) == old(buf)[(old(len) - at(before_block, len)) + k] }, 16u64 + k);
      apply(integer::uint8_pointer_add_associate_uint64(at(before_block, buf), 16u64, k));
      have buf + k == at(before_block, buf + (16u64 + k)) by {
       rewrite(buf, at(before_block, buf) + 16);
       close();
      }
      have load<uint8>(buf + k) == at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + (16u64 + k)))) by {
       rewrite(buf + k, at(before_block, buf + (16u64 + k)));
       close();
      }
      have (old(len) - len) + k == (old(len) - at(before_block, len)) + (16u64 + k) by {
       rewrite(old(len) - len, (old(len) - at(before_block, len)) + 16u64);
       close() using { to_integer((old(len) - at(before_block, len))) <= 5535; to_integer(k) <= 5551; };
      }
      have old(buf) + ((old(len) - len) + k) == old(buf) + ((old(len) - at(before_block, len)) + (16u64 + k)) by {
       rewrite((old(len) - len) + k, (old(len) - at(before_block, len)) + (16u64 + k));
       close();
      }
      have old(buf)[(old(len) - len) + k] == old(buf)[(old(len) - at(before_block, len)) + (16u64 + k)] by {
       close() using { old(buf) + ((old(len) - len) + k) == old(buf) + ((old(len) - at(before_block, len)) + (16u64 + k)); };
      }
      rewrite(old(buf)[(old(len) - len) + k], old(buf)[(old(len) - at(before_block, len)) + (16u64 + k)]);
      rewrite(load<uint8>(buf + k), at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + (16u64 + k)))));
      close() using { at(statement(8).statement(0).statement(42).statement(1).exit, load<uint8>(at(before_block, buf + (16u64 + k)))) == old(buf)[(old(len) - at(before_block, len)) + (16u64 + k)]; };
     }
    }
   }

   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), at(before_block, len)) + 16); close(); }
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), at(before_block, len)) + 16); close(); }
   have to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), at(before_block, len)) + 16); close(); }
   have to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len)) by { rewrite(zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), at(before_block, len)) + 16); close(); }
  }
 }
 have len <= 15u64 by close() using { not (len >= 16u64); len <= old(len); old(len) <= 5551u64; };
 have to_integer(len) <= to_integer(15u64);
 step_until(loop(4).entry);
 have to_integer(old(len)) <= to_integer(5551u64);
 have to_integer(len) <= to_integer(old(len));
 have to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
 have old(len) - len <= 22208u64 by close() using { old(len) - len <= 5551u64; };
 apply(zlib_prefix_observation(old(len), len));
 apply(adler_sum_nonnegative(old(buf), zlib_prefix_count(old(len), len)));
 have 1 <= to_integer(adler) by close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); 0 <= adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); };
 have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
 have 0 <= to_integer(sum2); have to_integer(sum2) <= 18446744073709551615;
 have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by {
  rewrite(to_integer(old(len)) - to_integer(len), to_integer(old(len) - len));
  rewrite(to_integer(old(len) - len), to_integer(zlib_prefix_count(old(len), len)));
  close() using { to_integer(adler) <= 1 + 255 * to_integer(zlib_prefix_count(old(len), len)); };
 }
 have to_integer(adler) <= 1415761 by close() using { to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)); to_integer(old(len)) <= 5551; 0 <= to_integer(len); };
 have to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)) by {
  rewrite(to_integer(old(len)) - to_integer(len), to_integer(old(len) - len));
  rewrite(to_integer(old(len) - len), to_integer(zlib_prefix_count(old(len), len)));
  close() using { to_integer(sum2) <= 1415761 * to_integer(zlib_prefix_count(old(len), len)); };
 }
 have to_integer(sum2) <= 7858889311 by close() using { to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)); to_integer(old(len)) <= 5551; 0 <= to_integer(len); };
// The scalar tail inherits the caller's complete input view. Its prefix
 // invariants locate each original read within that unchanged range.
 loop {
  decreases to_integer(len);
  invariant forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] };
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
  initialize by { close(); }
  maintain by {
   if len == 0u64 {
    have old(len) - len == old(len) by close();
    have zlib_prefix_count(old(len), len) == old(len as uint32 as int32) by {
     unfold(zlib_prefix_count(old(len), len));
     close();
    }
    have to_integer(adler) == 1 + adler_byte_sum(old(buf), old(len as uint32 as int32)) by {
     close() using { to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    have to_integer(sum2) == to_integer(old(len as uint32 as int32)) + adler_weighted_sum(old(buf), old(len as uint32 as int32), old(len as uint32 as int32)) by {
     close() using { to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)); zlib_prefix_count(old(len), len) == old(len as uint32 as int32); };
    }
    step(); step();
   } else {
    have 0u64 <= len by close();
    have 0u64 < len by close() using { 0u64 <= len; not(len == 0u64); };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have to_integer(0u64) < to_integer(len);
   have to_integer(1u64) <= to_integer(len) by close() using { to_integer(0u64) < to_integer(len); };
   have 1u64 <= len;
   have to_integer(len - 1u64) == to_integer(len) - to_integer(1u64);
   have len <= 15u64;
   have viewable(buf[0u64..1u64]) by close();
   have viewable(buf[0u64..len]) by close();
   mark before_decrement;
   have forall (k: uint64) { k < at(before_decrement, len) implies at(before_decrement, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_decrement, len)) + k] } by {
    intro() {
     intro() {
      have k < len by close();
      instantiate(forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] }, k);
      close() using { load<uint8>(buf + k) == old(buf)[(old(len) - len) + k]; };
     }
    }
   }
   step(); step();
   have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by close();
   have to_integer(len) <= 15 by close() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; at(before_decrement, to_integer(len)) <= 15; };
   have 0 <= to_integer(len) by close() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; to_integer(1u64) <= at(before_decrement, to_integer(len)); };
   have to_integer(len) < at(before_decrement, to_integer(len)) by close() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
   step_until(assignment(adler, 38).entry);
   have at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len)) by close();
   have at(before_decrement, len) <= old(len) by close();
   have to_integer(at(before_decrement, len)) <= to_integer(old(len));
   have to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - to_integer(at(before_decrement, len));
   have to_integer(old(len) - at(before_decrement, len)) < to_integer(old(len)) by close() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) < old(len);
   have old(len) <= 5551u64;
   have to_integer(old(len) - at(before_decrement, len)) <= 5550 by close() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) <= 5550u64;
   have old(len) - at(before_decrement, len) <= 22208u64 by close() using { old(len) - at(before_decrement, len) <= 5550u64; };
   have old(len) - at(before_decrement, len) <= 5551u64 by close() using { old(len) - at(before_decrement, len) <= 5550u64; };
   apply(zlib_prefix_pointer(old(buf), old(len), at(before_decrement, len)));
   have at(before_decrement, buf) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) by close() using {
    at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
    old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   have at(before_decrement, buf[0]) == old(buf)[zlib_prefix_count(old(len), at(before_decrement, len))] by close() using {
    at(before_decrement, buf) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
   };
   apply(zlib_byte_u64(at(before_decrement, buf[0])));
   apply(zlib_byte_integer_identity(at(before_decrement, buf[0])));
   have to_integer(adler) <= 1415251 by close() using {
    to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have to_integer(adler) + to_integer(at(before_decrement, buf[0]) as uint32 as uint64) <= 18446744073709551615 by close() using {
    to_integer(adler) <= 1415251;
    to_integer(at(before_decrement, buf[0]) as uint32 as uint64) == to_integer(at(before_decrement, buf[0]) as int32);
    to_integer(at(before_decrement, buf[0]) as int32) <= 255;
   };
   have to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64) == to_integer(adler) + to_integer(at(before_decrement, buf[0]) as uint32 as uint64);
   mark before_add;
   step();
   have adler == at(before_add, adler + at(before_decrement, buf[0]) as uint32 as uint64) by close();
   have to_integer(adler) == at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)) by {
    rewrite(adler, at(before_add, adler + at(before_decrement, buf[0]) as uint32 as uint64));
    rewrite(at(before_add, to_integer(adler) + to_integer(at(before_decrement, buf[0]) as uint32 as uint64)), at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)));
    close();
   }
   have to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as int32)) by close() using {
    to_integer(adler) == at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64));
    at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as uint32 as uint64));
    at(before_add, to_integer(at(before_decrement, buf[0]) as uint32 as uint64)) == at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
   };
   have 1 <= to_integer(adler) by close() using {
    1 <= at(before_add, to_integer(adler));
    0 <= at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
   };
   have to_integer(adler) <= 1 + 255 * (to_integer(old(len)) - to_integer(len)) by close() using {
    at(before_add, to_integer(adler)) <= 1 + 255 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    at(before_add, to_integer(at(before_decrement, buf[0]) as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(adler) <= 1415761 by close() using {
    at(before_add, to_integer(adler)) <= 1415251;
    at(before_add, to_integer(at(before_decrement, buf[0]) as int32)) <= 255;
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
   };
   have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by close() using {
    to_integer(sum2) <= 7858889311;
    to_integer(adler) <= 1415761;
   };
   have to_integer(sum2 + adler) == to_integer(sum2) + to_integer(adler);
   mark before_sum;
   step_until(loop.back_edge);
   have separate(statement(8).statement(1).statement(1).footprint, at(before_decrement, memory(buf[0u64..len]))) by close();
   have viewable(at(before_decrement, memory(buf[0u64..len]))) by {
    preserve(at(before_decrement, memory(buf[0u64..len])), statement(8).statement(1).statement(1));
   }
   have forall (k: uint64) { k < at(before_decrement, len) implies at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == old(buf)[(old(len) - at(before_decrement, len)) + k] } by {
    intro() {
     intro() {
      have separate(statement(8).statement(1).statement(1).footprint, at(before_decrement, memory((buf + k)[0..1]))) by close();
      have at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) by {
       preserve(at(before_decrement, memory((buf + k)[0..1])), statement(8).statement(1).statement(1));
      }
      have at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) == at(before_decrement, load<uint8>(buf + k)) by close();
      instantiate(forall (k: uint64) { k < at(before_decrement, len) implies at(before_decrement, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_decrement, len)) + k] }, k);
      close() using {
       at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k)));
       at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) == at(before_decrement, load<uint8>(buf + k));
       at(before_decrement, load<uint8>(buf + k)) == old(buf)[(old(len) - at(before_decrement, len)) + k];
      };
     }
    }
   }
   have to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler) by close();
   have 0 <= to_integer(sum2);
   have to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len)) by close() using {
    at(before_sum, to_integer(sum2)) <= 1415761 * (to_integer(old(len)) - at(before_decrement, to_integer(len)));
    to_integer(adler) <= 1415761;
    to_integer(sum2) == at(before_sum, to_integer(sum2)) + to_integer(adler);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };
   have to_integer(sum2) <= 7858889311 by close() using {
    to_integer(sum2) <= 1415761 * (to_integer(old(len)) - to_integer(len));
    to_integer(old(len)) <= 5551;
    0 <= to_integer(len);
   };
   have to_integer(len) <= to_integer(old(len)) by close() using {
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have len <= old(len);
   have to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
   have to_integer(old(len) - at(before_decrement, len)) <= 5550 by close() using {
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(old(len)) <= 5551;
    to_integer(1u64) <= at(before_decrement, to_integer(len));
   };
   have (old(len) - at(before_decrement, len)) <= 5550u64;
   have to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64) <= 18446744073709551615 by {
    apply(integer::add_le(to_integer(old(len) - at(before_decrement, len)), 5550, 1, 1));
    apply(integer::le_transitive(to_integer(old(len) - at(before_decrement, len)) + 1, 5551, 18446744073709551615));
   }
   have to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   have to_integer(old(len) - len) == to_integer((old(len) - at(before_decrement, len)) + 1u64) by close() using {
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer((old(len) - at(before_decrement, len)) + 1u64) == to_integer(old(len) - at(before_decrement, len)) + to_integer(1u64);
   };
   have (old(len) - len) == ((old(len) - at(before_decrement, len)) + 1u64);
   have buf == at(before_decrement, buf) + 1 by close();
   apply(integer::uint8_pointer_add_associate_uint64(old(buf), old(len) - at(before_decrement, len), 1u64));
   have buf == old(buf) + (old(len) - len) by {
    rewrite(buf, at(before_decrement, buf) + 1);
    rewrite(at(before_decrement, buf), old(buf) + (old(len) - at(before_decrement, len)));
    rewrite(old(len) - len, (old(len) - at(before_decrement, len)) + 1u64);
    close();
   }
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by close();
   have len == (at(before_decrement, len) - 1u64);
   have len <= at(before_decrement, len) - 1u64 by close();
   have len <= 15u64;
   have len <= 9223372036854775807u64;
   have to_integer(len) <= 5551 by close() using { len <= 15u64; };
   apply(click::separation::contains_subrange(at(before_decrement, buf), 0u64, at(before_decrement, len), 1u64, at(before_decrement, len)));
   apply(click::separation::contains_rebase(at(before_decrement, buf), 1u64, at(before_decrement, len)));
   have contains(memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]), memory(buf[0u64..len])) by {
    rewrite(buf, at(before_decrement, buf) + 1);
    rewrite(len, at(before_decrement, len - 1u64));
    apply(click::separation::contains_rebase(at(before_decrement, buf), 1u64, at(before_decrement, len)));
   }
   apply(click::separation::contains_trans(at(before_decrement, memory(buf[0u64..len])), memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]), memory(buf[0u64..len])));
   apply(click::separation::viewable_restrict(at(before_decrement, memory(buf[0u64..len])), memory(buf[0u64..len])));
   have forall (k: uint64) { k < len implies load<uint8>(buf + k) == old(buf)[(old(len) - len) + k] } by {
    intro() {
     intro() {
      have to_integer(k) <= 5551 by close() using { k < len; to_integer(len) <= 5551; };
      have 1 + to_integer(k) <= 18446744073709551615 by close() using { to_integer(k) <= 5551; };
      apply(integer::uint64_add_to_integer(1u64, k));
      have 1u64 + k < at(before_decrement, len) by close() using {
       k < len;
       to_integer(len) == at(before_decrement, to_integer(len)) - 1;
       to_integer(1u64 + k) == to_integer(1u64) + to_integer(k);
      };
      instantiate(forall (k: uint64) { k < at(before_decrement, len) implies at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == old(buf)[(old(len) - at(before_decrement, len)) + k] }, 1u64 + k);
      apply(integer::uint8_pointer_add_associate_uint64(at(before_decrement, buf), 1u64, k));
      have buf + k == at(before_decrement, buf + (1u64 + k)) by {
       rewrite(buf, at(before_decrement, buf) + 1);
       close();
      }
      have load<uint8>(buf + k) == at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))) by {
       rewrite(buf + k, at(before_decrement, buf + (1u64 + k)));
       close();
      }
      have (old(len) - len) + k == (old(len) - at(before_decrement, len)) + (1u64 + k) by {
       rewrite(old(len) - len, (old(len) - at(before_decrement, len)) + 1u64);
       close() using { to_integer((old(len) - at(before_decrement, len))) <= 5550; to_integer(k) <= 5551; };
      }
      have old(buf) + ((old(len) - len) + k) == old(buf) + ((old(len) - at(before_decrement, len)) + (1u64 + k)) by {
       rewrite((old(len) - len) + k, (old(len) - at(before_decrement, len)) + (1u64 + k));
       close();
      }
      have old(buf)[(old(len) - len) + k] == old(buf)[(old(len) - at(before_decrement, len)) + (1u64 + k)] by {
       close() using { old(buf) + ((old(len) - len) + k) == old(buf) + ((old(len) - at(before_decrement, len)) + (1u64 + k)); };
      }
      rewrite(old(buf)[(old(len) - len) + k], old(buf)[(old(len) - at(before_decrement, len)) + (1u64 + k)]);
      rewrite(load<uint8>(buf + k), at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))));
      close() using { at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))) == old(buf)[(old(len) - at(before_decrement, len)) + (1u64 + k)]; };
     }
    }
   }

   have old(len) - len <= 5551u64 by {
    have to_integer(old(len) - len) <= 5551 by close() using {
     to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
     to_integer(old(len)) <= 5551;
     0 <= to_integer(len);
    };
    have (old(len) - len) <= 5551u64;
   }
   have old(len) - len <= 22208u64 by close() using { old(len) - len <= 5551u64; };
   apply(zlib_prefix_observation(old(len), len));
   apply(zlib_prefix_observation(old(len), at(before_decrement, len)));
   have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1 by close() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(old(len) - len);
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - len) == to_integer(old(len)) - to_integer(len);
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    to_integer(len) == at(before_decrement, to_integer(len)) - 1;
   };

   have 0 < to_integer(zlib_prefix_count(old(len), len)) by close() using {
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
    to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) == to_integer(old(len) - at(before_decrement, len));
    to_integer(old(len) - at(before_decrement, len)) == to_integer(old(len)) - at(before_decrement, to_integer(len));
    at(before_decrement, to_integer(len)) <= to_integer(old(len));
   };
   have to_integer(1) <= to_integer(zlib_prefix_count(old(len), len)) by close() using { 0 < to_integer(zlib_prefix_count(old(len), len)); };
   have 1 <= zlib_prefix_count(old(len), len);
   apply(zlib_positive_count(zlib_prefix_count(old(len), len)));
   have defined(zlib_prefix_count(old(len), len) - 1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
   have to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) by close() using {
    to_integer(zlib_prefix_count(old(len), len) - 1) == to_integer(zlib_prefix_count(old(len), len)) - to_integer(1);
    to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len))) + 1;
   };
   apply(zlib_prefix_append(old(buf), old(len), len));
   apply(adler_weighted_prefix_step(old(buf), zlib_prefix_count(old(len), len)));
   have old(buf)[zlib_prefix_count(old(len), len) - 1] == at(before_add, at(before_decrement, buf[0])) by {
    rewrite(zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), at(before_decrement, len)));
    close();
   }
   have adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len))) by {
    rewrite(zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), at(before_decrement, len)));
    close();
   }
   have adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), len) - 1) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), zlib_prefix_count(old(len), at(before_decrement, len))) by {
    rewrite(zlib_prefix_count(old(len), len) - 1, zlib_prefix_count(old(len), at(before_decrement, len)));
    close();
   }
   apply(zlib_equal_byte_integers(old(buf)[zlib_prefix_count(old(len), len) - 1], at(before_add, at(before_decrement, buf[0]))));
   have zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(at(before_decrement, buf[0]) as int32)) by {
    rewrite(zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]), zlib_byte_integer(at(before_add, at(before_decrement, buf[0]))));
    close() using { at(before_add, zlib_byte_integer(at(before_decrement, buf[0]))) == at(before_add, to_integer(at(before_decrement, buf[0]) as int32)); };
   }
   have to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) by close() using {
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len)) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) + zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]);
    adler_byte_sum(old(buf), zlib_prefix_count(old(len), len) - 1) == adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
    zlib_byte_integer(old(buf)[zlib_prefix_count(old(len), len) - 1]) == at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
    to_integer(adler) == at(before_add, to_integer(adler)) + at(before_add, to_integer(at(before_decrement, buf[0]) as int32));
    at(before_add, to_integer(adler)) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)));
   };
   have to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len)) by close() using {
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
 step_until(assignment(adler, 39).entry);
 apply(zlib_reduced_result(old(buf), old(len as uint32 as int32), adler, sum2));
}
