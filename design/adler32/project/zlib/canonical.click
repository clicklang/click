import click::integer;
target "x86_64-unknown-linux-gnu";
verifying "../../vendor/zlib-1.3.1/adler32.c";
import "canonical-helpers.click";
theorem zlib_canonical_weighted_sum_count_equal(bytes: uint8[], first: int32, last: int32) {
 requires first == last;
 ensures adler_weighted_sum(bytes, first, first) == adler_weighted_sum(bytes, last, last) by {
  rewrite(first, last);
  close();
 }
}
uint64 adler32_z(uint64 adler, const uint8* buf, uint64 len) {
 requires zlib_seed_a(adler) <= 65520u64;
 requires zlib_seed_b(adler) <= 65520u64;
 requires buf != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
 } by {
 have len <= 9223372036854775807u64 by close();
 if len == 1u64 {
  have len <= 2147483647u64 by close() using { len == 1u64; };
  have to_integer(len as uint32 as int32) == to_integer(len) by {
   close() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
  }
  apply(adler_spec_checksum_bridge(buf, len as uint32 as int32, len, to_integer(zlib_seed_a(adler)), to_integer(zlib_seed_b(adler))));
apply(zlib_seed_bounds(adler));
 have old(len as uint32 as int32) == 1 by close();
 have viewable(buf[0u64..1u64]) by close();
 unfold(zlib_seed_a(adler)); unfold(zlib_seed_b(adler));
 step_until(assignment(adler, 0).entry); step();
 have adler == zlib_seed_a(old(adler)) by close();
 have sum2 == zlib_seed_b(old(adler)) by close();
 have adler <= 65520u64 by close(); have sum2 <= 65520u64 by close();
 apply(zlib_byte_u64(buf[0])); apply(zlib_byte_integer_identity(buf[0]));
 have to_integer(buf[0] as uint32 as uint64) == zlib_byte_integer(buf[0]) by {
  rewrite(to_integer(buf[0] as uint32 as uint64), to_integer(buf[0] as int32));
  rewrite(zlib_byte_integer(buf[0]), to_integer(buf[0] as int32));
  close();
 }
 have to_integer(adler) + to_integer(buf[0] as uint32 as uint64) <= 18446744073709551615 by close() using { to_integer(adler) <= 65520; to_integer(buf[0] as uint32 as uint64) == to_integer(buf[0] as int32); to_integer(buf[0] as int32) <= 255; };
 have to_integer(adler + buf[0] as uint32 as uint64) == to_integer(adler) + to_integer(buf[0] as uint32 as uint64);
 mark decoded;
 step_until(assignment(adler, 1).entry); step();
 have to_integer(adler) == to_integer(zlib_seed_a(old(adler))) + zlib_byte_integer(buf[0]) by {
  have to_integer(adler) == to_integer(at(decoded, adler + buf[0] as uint32 as uint64)) by close();
  rewrite(to_integer(adler), to_integer(at(decoded, adler + buf[0] as uint32 as uint64)));
  rewrite(at(decoded, to_integer(adler + buf[0] as uint32 as uint64)), at(decoded, to_integer(adler)) + to_integer(buf[0] as uint32 as uint64));
  rewrite(at(decoded, adler), zlib_seed_a(old(adler)));
  rewrite(to_integer(buf[0] as uint32 as uint64), zlib_byte_integer(buf[0])); close();
 }
 have adler <= 65775u64 by close() using { to_integer(adler) == to_integer(at(decoded, adler + buf[0] as uint32 as uint64)); at(decoded, to_integer(adler + buf[0] as uint32 as uint64)) == at(decoded, to_integer(adler)) + to_integer(buf[0] as uint32 as uint64); at(decoded, adler) <= 65520u64; buf[0] as uint32 as uint64 <= 255u64; };
 mark raw_a;
 if adler >= 65521u64 {
  have 65521u64 <= adler by { close(); }
  have adler <= 131041u64 by close() using { adler <= 65775u64; };
  apply(zlib_reduce_once_above(adler));
  step_until(assignment(adler, 2).entry); step();
  have to_integer(adler) == to_integer(at(raw_a, adler - 65521u64)) by close();
  have adler <= 65520u64 by close();
  have to_integer(adler) == at(raw_a, to_integer(adler % 65521u64)) by { rewrite(to_integer(adler), to_integer(at(raw_a, adler - 65521u64))); close(); }
 
 step_until(assignment(sum2, 1).entry);
 have to_integer(adler) == truncating_remainder(to_integer(zlib_seed_a(old(adler))) + zlib_byte_integer(buf[0]), 65521) by {
  apply(integer::uint64_remainder_to_integer(at(raw_a, adler), 65521u64));
  rewrite(to_integer(zlib_seed_a(old(adler))) + zlib_byte_integer(buf[0]), at(raw_a, to_integer(adler)));
  have truncating_remainder(to_integer(at(raw_a, adler)), 65521) == at(raw_a, to_integer(adler % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_a, adler)), 65521), to_integer(at(raw_a, adler) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_a, adler)), 65521), at(raw_a, to_integer(adler % 65521u64)));
  close() using { to_integer(adler) == at(raw_a, to_integer(adler % 65521u64)); };
 }
 have sum2 == zlib_seed_b(old(adler)) by close();
 have sum2 <= 65520u64 by close();
 have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by close() using { to_integer(adler) <= 65520; to_integer(sum2) <= 65520; };
 apply(integer::uint64_add_to_integer(sum2, adler));
 mark reduced_a;
 step();
 have to_integer(sum2) == to_integer(at(reduced_a, sum2 + adler)) by close();
 have to_integer(sum2) == to_integer(zlib_seed_b(old(adler))) + to_integer(adler) by { rewrite(to_integer(sum2), to_integer(at(reduced_a, sum2 + adler))); rewrite(at(reduced_a, to_integer(sum2 + adler)), at(reduced_a, to_integer(sum2)) + to_integer(adler)); rewrite(at(reduced_a, sum2), zlib_seed_b(old(adler))); close(); }
 have sum2 <= 131040u64 by close() using { to_integer(sum2) == to_integer(at(reduced_a, sum2 + adler)); at(reduced_a, to_integer(sum2 + adler)) == at(reduced_a, to_integer(sum2)) + to_integer(adler); at(reduced_a, sum2) <= 65520u64; adler <= 65520u64; };
 mark raw_b;
 if sum2 >= 65521u64 {
  have 65521u64 <= sum2 by { close(); }
  have sum2 <= 131041u64 by close() using { sum2 <= 131040u64; };
  apply(zlib_reduce_once_above(sum2));
  step_until(assignment(sum2, 2).entry); step();
  have to_integer(sum2) == to_integer(at(raw_b, sum2 - 65521u64)) by close();
  have sum2 <= 65520u64 by close();
  have to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)) by { rewrite(to_integer(sum2), to_integer(at(raw_b, sum2 - 65521u64))); close(); }
 
 have to_integer(sum2) == truncating_remainder(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), 65521) by { apply(integer::uint64_remainder_to_integer(at(raw_b, sum2), 65521u64)); rewrite(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), at(raw_b, to_integer(sum2)));
  have truncating_remainder(to_integer(at(raw_b, sum2)), 65521) == at(raw_b, to_integer(sum2 % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), to_integer(at(raw_b, sum2) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), at(raw_b, to_integer(sum2 % 65521u64)));
  close() using { to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)); }; }
 apply(zlib_one_seeded_components(buf, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))), adler, sum2));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(old(len as uint32 as int32), 1); close(); }
 step_until(function.exit); close();

 } else {
  have sum2 < 65521u64 by { close(); }
  apply(zlib_reduce_once_below(sum2));
  have sum2 <= 65520u64 by close();
  have to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)) by close();
 
 have to_integer(sum2) == truncating_remainder(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), 65521) by { apply(integer::uint64_remainder_to_integer(at(raw_b, sum2), 65521u64)); rewrite(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), at(raw_b, to_integer(sum2)));
  have truncating_remainder(to_integer(at(raw_b, sum2)), 65521) == at(raw_b, to_integer(sum2 % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), to_integer(at(raw_b, sum2) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), at(raw_b, to_integer(sum2 % 65521u64)));
  close() using { to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)); }; }
 apply(zlib_one_seeded_components(buf, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))), adler, sum2));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(old(len as uint32 as int32), 1); close(); }
 step_until(function.exit); close();

 }

 } else {
  have adler < 65521u64 by { close(); }
  apply(zlib_reduce_once_below(adler));
  step_until(assignment(sum2, 1).entry);
  have adler <= 65520u64 by close();
  have to_integer(adler) == at(raw_a, to_integer(adler % 65521u64)) by close();
 
 step_until(assignment(sum2, 1).entry);
 have to_integer(adler) == truncating_remainder(to_integer(zlib_seed_a(old(adler))) + zlib_byte_integer(buf[0]), 65521) by {
  apply(integer::uint64_remainder_to_integer(at(raw_a, adler), 65521u64));
  rewrite(to_integer(zlib_seed_a(old(adler))) + zlib_byte_integer(buf[0]), at(raw_a, to_integer(adler)));
  have truncating_remainder(to_integer(at(raw_a, adler)), 65521) == at(raw_a, to_integer(adler % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_a, adler)), 65521), to_integer(at(raw_a, adler) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_a, adler)), 65521), at(raw_a, to_integer(adler % 65521u64)));
  close() using { to_integer(adler) == at(raw_a, to_integer(adler % 65521u64)); };
 }
 have sum2 == zlib_seed_b(old(adler)) by close();
 have sum2 <= 65520u64 by close();
 have to_integer(sum2) + to_integer(adler) <= 18446744073709551615 by close() using { to_integer(adler) <= 65520; to_integer(sum2) <= 65520; };
 apply(integer::uint64_add_to_integer(sum2, adler));
 mark reduced_a;
 step();
 have to_integer(sum2) == to_integer(at(reduced_a, sum2 + adler)) by close();
 have to_integer(sum2) == to_integer(zlib_seed_b(old(adler))) + to_integer(adler) by { rewrite(to_integer(sum2), to_integer(at(reduced_a, sum2 + adler))); rewrite(at(reduced_a, to_integer(sum2 + adler)), at(reduced_a, to_integer(sum2)) + to_integer(adler)); rewrite(at(reduced_a, sum2), zlib_seed_b(old(adler))); close(); }
 have sum2 <= 131040u64 by close() using { to_integer(sum2) == to_integer(at(reduced_a, sum2 + adler)); at(reduced_a, sum2) <= 65520u64; adler <= 65520u64; };
 mark raw_b;
 if sum2 >= 65521u64 {
  have 65521u64 <= sum2 by { close(); }
  have sum2 <= 131041u64 by close() using { sum2 <= 131040u64; };
  apply(zlib_reduce_once_above(sum2));
  step_until(assignment(sum2, 2).entry); step();
  have to_integer(sum2) == to_integer(at(raw_b, sum2 - 65521u64)) by close();
  have sum2 <= 65520u64 by close();
  have to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)) by { rewrite(to_integer(sum2), to_integer(at(raw_b, sum2 - 65521u64))); close(); }
 
 have to_integer(sum2) == truncating_remainder(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), 65521) by { apply(integer::uint64_remainder_to_integer(at(raw_b, sum2), 65521u64)); rewrite(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), at(raw_b, to_integer(sum2)));
  have truncating_remainder(to_integer(at(raw_b, sum2)), 65521) == at(raw_b, to_integer(sum2 % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), to_integer(at(raw_b, sum2) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), at(raw_b, to_integer(sum2 % 65521u64)));
  close() using { to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)); }; }
 apply(zlib_one_seeded_components(buf, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))), adler, sum2));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(old(len as uint32 as int32), 1); close(); }
 step_until(function.exit); close();

 } else {
  have sum2 < 65521u64 by { close(); }
  apply(zlib_reduce_once_below(sum2));
  have sum2 <= 65520u64 by close();
  have to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)) by close();
 
 have to_integer(sum2) == truncating_remainder(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), 65521) by { apply(integer::uint64_remainder_to_integer(at(raw_b, sum2), 65521u64)); rewrite(to_integer(zlib_seed_b(old(adler))) + to_integer(adler), at(raw_b, to_integer(sum2)));
  have truncating_remainder(to_integer(at(raw_b, sum2)), 65521) == at(raw_b, to_integer(sum2 % 65521u64)) by {
   rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), to_integer(at(raw_b, sum2) % 65521u64));
   close();
  }
  rewrite(truncating_remainder(to_integer(at(raw_b, sum2)), 65521), at(raw_b, to_integer(sum2 % 65521u64)));
  close() using { to_integer(sum2) == at(raw_b, to_integer(sum2 % 65521u64)); }; }
 apply(zlib_one_seeded_components(buf, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))), adler, sum2));
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(old(len as uint32 as int32), 1); close(); }
 step_until(function.exit); close();

 }

 }
 } else {
  if len <= 15u64 {
  have len <= 2147483647u64 by close() using { len <= 15u64; };
  have to_integer(len as uint32 as int32) == to_integer(len) by {
   close() using { 0 <= to_integer(len); to_integer(len) <= 2147483647; };
  }
  apply(adler_spec_checksum_bridge(buf, len as uint32 as int32, len, to_integer(zlib_seed_a(adler)), to_integer(zlib_seed_b(adler))));
have viewable(buf[0u64..len]) by close();
 apply(zlib_seed_bounds(adler));
 unfold(zlib_seed_a(adler)); unfold(zlib_seed_b(adler));
 step_until(loop(0).entry);
 have adler == zlib_seed_a(old(adler)) by close();
 have sum2 == zlib_seed_b(old(adler)) by close();
 have adler <= 65520u64 by close(); have sum2 <= 65520u64 by close();
 have to_integer(adler) == to_integer(zlib_seed_a(old(adler))) by { rewrite(adler, zlib_seed_a(old(adler))); close(); }
 have to_integer(sum2) == to_integer(zlib_seed_b(old(adler))) by { rewrite(sum2, zlib_seed_b(old(adler))); close(); }
 have adler < 65521u64 by close() using { adler <= 65520u64; };
 have sum2 < 65521u64 by close() using { sum2 <= 65520u64; };
 apply(zlib_reduce_once_below(adler)); apply(zlib_reduce_once_below(sum2));
 apply(adler_spec_empty(old(buf), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
 have zlib_prefix_count(old(len), len) == 0 by { unfold(zlib_prefix_count(old(len), len)); close(); }
 have to_integer(adler % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), to_integer(zlib_seed_a(old(adler)))) by { rewrite(zlib_prefix_count(old(len), len), 0); close() using { to_integer(adler) == to_integer(zlib_seed_a(old(adler))); to_integer(adler) == to_integer(adler % 65521u64); adler_spec_a(old(buf), 0, to_integer(zlib_seed_a(old(adler)))) == to_integer(zlib_seed_a(old(adler))); }; }
 have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(zlib_prefix_count(old(len), len), 0); close() using { to_integer(sum2) == to_integer(zlib_seed_b(old(adler))); to_integer(sum2) == to_integer(sum2 % 65521u64); adler_spec_b(old(buf), 0, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) == to_integer(zlib_seed_b(old(adler))); }; }
  loop {
   decreases to_integer(len);
  invariant 0 <= to_integer(zlib_seed_a(old(adler)));
  invariant to_integer(zlib_seed_a(old(adler))) <= 65520;
  invariant 0 <= to_integer(zlib_seed_b(old(adler)));
   invariant len <= at(loop(0).entry, len);
   invariant at(loop(0).entry, len) <= 15u64;
   invariant at(loop(0).entry, len) <= old(len);
   invariant old(len) <= 2147483647u64;
   invariant len <= old(len);
   invariant buf == at(loop(0).entry, buf) + (at(loop(0).entry, len) - len);
   invariant buf == old(buf) + (old(len) - len);
   invariant at(loop(0).entry, buf) == old(buf) + (old(len) - at(loop(0).entry, len));
   invariant viewable(buf[0u64..len]);
   invariant at(loop(0).entry, adler) <= 65520u64;
   invariant at(loop(0).entry, sum2) <= 65520u64;
   invariant to_integer(at(loop(0).entry, adler) % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), at(loop(0).entry, len)), to_integer(zlib_seed_a(old(adler))));
   invariant to_integer(at(loop(0).entry, sum2) % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), at(loop(0).entry, len)), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
   invariant to_integer(adler) == to_integer(at(loop(0).entry, adler)) + adler_byte_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len));
   invariant to_integer(sum2) == to_integer(at(loop(0).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) * to_integer(at(loop(0).entry, adler)) + adler_weighted_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len), zlib_prefix_count(at(loop(0).entry, len), len));
   invariant to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len));
   invariant to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len));
   initialize by {
    have len <= 9223372036854775807u64 by close() using { len <= 15u64; };
    have zlib_prefix_count(at(loop(0).entry, len), len) == 0 by { unfold(zlib_prefix_count(at(loop(0).entry, len), len)); close(); }
    apply(adler_sum_empty(at(loop(0).entry, buf), 0));
    have to_integer(adler) == to_integer(at(loop(0).entry, adler)) + adler_byte_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(0).entry, len), len), 0); close() using { adler_byte_sum(at(loop(0).entry, buf), 0) == 0; }; }
    have to_integer(sum2) == to_integer(at(loop(0).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) * to_integer(at(loop(0).entry, adler)) + adler_weighted_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len), zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(0).entry, len), len), 0); close() using { adler_weighted_sum(at(loop(0).entry, buf), 0, 0) == 0; }; }
    have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(0).entry, len), len), 0); close() using { to_integer(adler) <= 65520; }; }
    have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(0).entry, len), len), 0); close() using { to_integer(sum2) <= 65520; }; }
    close();
   }
   maintain by {
    if len == 0u64 {
     // Record the checksum before the zero guard decrements len to UINT64_MAX.
     have to_integer(old(len) - at(loop(0).entry, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(old(len), at(loop(0).entry, len)));
      have to_integer(old(len)) <= 2147483647 by close() using { old(len) <= 2147483647u64; };
      have 0 <= to_integer(at(loop(0).entry, len)) by close();
      rewrite(to_integer(old(len) - at(loop(0).entry, len)), to_integer(old(len)) - to_integer(at(loop(0).entry, len)));
      apply(integer::subtract_le(to_integer(old(len)), 2147483647, to_integer(at(loop(0).entry, len)), 0));
      close();
     }
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), len));
      have to_integer(at(loop(0).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(0).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(0).entry, len) - len), to_integer(at(loop(0).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_observation(old(len), at(loop(0).entry, len))); apply(zlib_full_prefix_observation(at(loop(0).entry, len), len));
     apply(zlib_full_prefix_pointer(old(buf), old(len), at(loop(0).entry, len)));
     have at(loop(0).entry, buf) == old(buf) + zlib_prefix_count(old(len), at(loop(0).entry, len)) by close();
     apply(zlib_full_concat_bound(old(len), at(loop(0).entry, len), len));
     have defined(zlib_prefix_count(old(len), at(loop(0).entry, len)) + zlib_prefix_count(at(loop(0).entry, len), len)) by close();
     have to_integer(adler) == to_integer(at(loop(0).entry, adler)) + adler_byte_sum(old(buf) + zlib_prefix_count(old(len), at(loop(0).entry, len)), zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(0).entry, len)), at(loop(0).entry, buf)); close(); }
  have to_integer(sum2) == to_integer(at(loop(0).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) * to_integer(at(loop(0).entry, adler)) + adler_weighted_sum(old(buf) + zlib_prefix_count(old(len), at(loop(0).entry, len)), zlib_prefix_count(at(loop(0).entry, len), len), zlib_prefix_count(at(loop(0).entry, len), len)) by { rewrite(old(buf) + zlib_prefix_count(old(len), at(loop(0).entry, len)), at(loop(0).entry, buf)); close(); }
  have at(loop(0).entry, adler) <= 1500000u64 by close() using { at(loop(0).entry, adler) <= 65520u64; };
  apply(zlib_general_raw_seeded_batch_concat(old(buf), zlib_prefix_count(old(len), at(loop(0).entry, len)), zlib_prefix_count(at(loop(0).entry, len), len), adler, sum2, at(loop(0).entry, adler), at(loop(0).entry, sum2), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
     apply(zlib_full_stream_split_count(old(len), at(loop(0).entry, len), len));
     have zlib_prefix_count(old(len), len) == old(len as uint32 as int32) by { unfold(zlib_prefix_count(old(len), len)); close(); }
     have to_integer(adler % 65521u64) == adler_spec_a(old(buf), zlib_prefix_count(old(len), len), to_integer(zlib_seed_a(old(adler)))) by { rewrite(to_integer(zlib_prefix_count(old(len), len)), to_integer(zlib_prefix_count(old(len), at(loop(0).entry, len)) + zlib_prefix_count(at(loop(0).entry, len), len))); close(); }
     have to_integer(adler % 65521u64) == adler_spec_a(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler)))) by { rewrite(old(len as uint32 as int32), zlib_prefix_count(old(len), len)); close(); }
     have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), zlib_prefix_count(old(len), len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(to_integer(zlib_prefix_count(old(len), len)), to_integer(zlib_prefix_count(old(len), at(loop(0).entry, len)) + zlib_prefix_count(at(loop(0).entry, len), len))); close(); }
     have to_integer(sum2 % 65521u64) == adler_spec_b(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(old(len as uint32 as int32), zlib_prefix_count(old(len), len)); close(); }
     apply(zlib_general_components_pack(old(buf), old(len as uint32 as int32), adler, sum2, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
     apply(zlib_full_prefix_observation(at(loop(0).entry, len), len));
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(15u64) by close() using { at(loop(0).entry, len) <= 15u64; len == 0u64; };
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(15u64);
     have to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) <= 15 by {
      rewrite(to_integer(zlib_prefix_count(at(loop(0).entry, len), len)), to_integer(at(loop(0).entry, len) - len));
      close() using { to_integer(at(loop(0).entry, len) - len) <= 15; };
     }
     have to_integer(adler) <= 69345 by close() using { to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len)); to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) <= 15; };
     have adler <= 69345u64;
     step(); step();
    } else {
     have 0u64 <= len by close();
     have 0u64 < len by {
      if 0u64 < len { close(); } else {
       have 0u64 == len;
       have len == 0u64 by { rewrite(0u64, len); close(); }
       contradiction(len == 0u64);
      }
     }
     have to_integer(0u64) < to_integer(len);
     have to_integer(1u64) <= to_integer(len) by close() using { to_integer(0u64) < to_integer(len); };
     have 1u64 <= len;
     have len <= 15u64 by close() using { len <= at(loop(0).entry, len); at(loop(0).entry, len) <= 15u64; };
     have to_integer(len - 1u64) == to_integer(len) - to_integer(1u64);
     have at(loop(0).entry, len) <= 2147483647u64 by {
      apply(integer::uint64_less_equal_transitive(at(loop(0).entry, len), 15u64, 2147483647u64));
     }
     apply(zlib_full_stream_remaining_step(at(loop(0).entry, len), len, 1u64));
     apply(zlib_full_stream_prefix_step(at(loop(0).entry, len), len, 1u64));
     apply(zlib_full_stream_prefix_step(old(len), len, 1u64));
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), len));
      have to_integer(at(loop(0).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(0).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(0).entry, len) - len), to_integer(at(loop(0).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_observation(at(loop(0).entry, len), len));
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(15u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), len));
      have to_integer(at(loop(0).entry, len)) <= 15 by close() using { at(loop(0).entry, len) <= 15u64; };
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(0).entry, len) - len), to_integer(at(loop(0).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 15, to_integer(len), 0));
      close();
     }
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(15u64);
     have to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) <= to_integer(15) by {
      rewrite(to_integer(zlib_prefix_count(at(loop(0).entry, len), len)), to_integer(at(loop(0).entry, len) - len));
      close() using { to_integer(at(loop(0).entry, len) - len) <= to_integer(15u64); };
     }
     have zlib_prefix_count(at(loop(0).entry, len), len) <= 15;
     have 15 < 16 by close();
     have zlib_prefix_count(at(loop(0).entry, len), len) < 16;
     have viewable(buf[0u64..1u64]) by close();
     have viewable(buf[0u64..len]) by close();
     mark before_decrement;
     step(); step();
     have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by close();
     have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by close();
     step_until(assignment(adler, 3).entry);
     apply(zlib_full_stream_scalar_read_bound(old(len), at(before_decrement, len)));
     have to_integer(at(loop(0).entry, len) - at(before_decrement, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), at(before_decrement, len)));
      have to_integer(at(loop(0).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(0).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(at(before_decrement, len)) by close();
      rewrite(to_integer(at(loop(0).entry, len) - at(before_decrement, len)), to_integer(at(loop(0).entry, len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 2147483647, to_integer(at(before_decrement, len)), 0));
      close();
     }
     apply(zlib_full_prefix_pointer(at(loop(0).entry, buf), at(loop(0).entry, len), at(before_decrement, len)));
     have at(before_decrement, buf) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) by {
      rewrite(at(before_decrement, buf), at(loop(0).entry, buf) + (at(loop(0).entry, len) - at(before_decrement, len)));
      close() using { at(loop(0).entry, buf) + (at(loop(0).entry, len) - at(before_decrement, len)) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)); };
     }
     have at(before_decrement, &buf[0]) == at(before_decrement, buf) by close();
     have at(before_decrement, &buf[0]) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) by {
      rewrite(at(before_decrement, &buf[0]), at(before_decrement, buf));
      close() using { at(before_decrement, buf) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)); };
     }
     have at(before_decrement, buf[0]) == at(before_decrement, load<uint8>(at(before_decrement, &buf[0]))) by close();
     have at(before_decrement, load<uint8>(at(before_decrement, &buf[0]))) == at(before_decrement, load<uint8>(at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)))) by {
      rewrite(at(before_decrement, &buf[0]), at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)));
      close();
     }
     have at(before_decrement, load<uint8>(at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)))) == at(loop(0).entry, buf)[zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))] by close();
     have at(before_decrement, buf[0]) == at(loop(0).entry, buf)[zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))] by close() using {
      at(before_decrement, load<uint8>(at(before_decrement, &buf[0]))) == at(before_decrement, load<uint8>(at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))));
     };
     have to_integer(at(loop(0).entry, len) - at(before_decrement, len)) <= to_integer(14u64) by close() using { at(loop(0).entry, len) <= 15u64; 1u64 <= at(before_decrement, len); at(before_decrement, len) <= at(loop(0).entry, len); };
     apply(zlib_full_prefix_observation(at(loop(0).entry, len), at(before_decrement, len)));
     have to_integer(at(loop(0).entry, len) - at(before_decrement, len)) <= to_integer(14u64);
     have to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))) <= to_integer(14) by {
      rewrite(to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))), to_integer(at(loop(0).entry, len) - at(before_decrement, len)));
      close() using { to_integer(at(loop(0).entry, len) - at(before_decrement, len)) <= 14; };
     }
     have zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) <= 14;
     apply(zlib_short_count_limit(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len))));
     apply(zlib_seeded_component_step(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)), adler, sum2, at(before_decrement, buf[0]), at(loop(0).entry, adler), at(loop(0).entry, sum2)));
     mark before_add;
     step(); step_until(assignment(sum2, 3).entry); step();
     have to_integer(adler) == to_integer(at(before_add, adler + at(before_decrement, buf[0]) as uint32 as uint64)) by close();
     have to_integer(sum2) == to_integer(at(before_add, sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))) by close();
     have to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) by close();
     have zlib_prefix_count(at(loop(0).entry, len), len) == (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32 by close() using { to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1); };
     have to_integer(adler) == to_integer(at(loop(0).entry, adler)) + adler_byte_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len)) by {
      rewrite(to_integer(adler), at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)));
      rewrite(zlib_prefix_count(at(loop(0).entry, len), len), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64) == to_integer(at(loop(0).entry, adler)) + adler_byte_sum(at(loop(0).entry, buf), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(sum2) == to_integer(at(loop(0).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) * to_integer(at(loop(0).entry, adler)) + adler_weighted_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len), zlib_prefix_count(at(loop(0).entry, len), len)) by {
      rewrite(to_integer(sum2), at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))));
      apply(zlib_canonical_weighted_sum_count_equal(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32));
      rewrite(adler_weighted_sum(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), len), zlib_prefix_count(at(loop(0).entry, len), len)), adler_weighted_sum(at(loop(0).entry, buf), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1)));
      rewrite(zlib_prefix_count(at(loop(0).entry, len), len), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64)) == to_integer(at(loop(0).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1)) * to_integer(at(loop(0).entry, adler)) + adler_weighted_sum(at(loop(0).entry, buf), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) by {
      rewrite(to_integer(adler), at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)));
      rewrite(zlib_prefix_count(at(loop(0).entry, len), len), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) by {
      rewrite(to_integer(sum2), at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))));
      rewrite(zlib_prefix_count(at(loop(0).entry, len), len), (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64)) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1))); };
     }
     have len <= at(before_decrement, len) by {
      have to_integer(len) <= to_integer(at(before_decrement, len)) by close() using {
       to_integer(len) == at(before_decrement, to_integer(len)) - 1;
      };
      apply(integer::uint64_to_integer_less_equal_implies_less_equal(len, at(before_decrement, len)));
     }
     have len <= at(loop(0).entry, len) by close() using { len <= at(before_decrement, len); at(before_decrement, len) <= at(loop(0).entry, len); at(loop(0).entry, len) <= 2147483647u64; };
     have to_integer(at(loop(0).entry, len) - at(before_decrement, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), at(before_decrement, len)));
      have to_integer(at(loop(0).entry, len)) <= 2147483647 by close() using { at(loop(0).entry, len) <= 2147483647u64; };
      have 0 <= to_integer(at(before_decrement, len)) by close();
      rewrite(to_integer(at(loop(0).entry, len) - at(before_decrement, len)), to_integer(at(loop(0).entry, len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 2147483647, to_integer(at(before_decrement, len)), 0));
      close();
     }
     have to_integer(at(loop(0).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(0).entry, len), len));
      have to_integer(at(loop(0).entry, len)) <= 2147483647 by close() using { at(loop(0).entry, len) <= 2147483647u64; };
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(0).entry, len) - len), to_integer(at(loop(0).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(0).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_pointer(at(loop(0).entry, buf), at(loop(0).entry, len), at(before_decrement, len))); apply(zlib_full_prefix_pointer(at(loop(0).entry, buf), at(loop(0).entry, len), len));
     have to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) by close();
     have defined(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1) by close();
     apply(click::integer::uint8_pointer_add_associate_int32(at(loop(0).entry, buf), zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)), 1));
     have buf == at(loop(0).entry, buf) + (at(loop(0).entry, len) - len) by close() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == at(loop(0).entry, buf) + (at(loop(0).entry, len) - at(before_decrement, len));
      at(loop(0).entry, buf) + (at(loop(0).entry, len) - at(before_decrement, len)) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len));
      at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1 == at(loop(0).entry, buf) + (zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1);
      to_integer(zlib_prefix_count(at(loop(0).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(0).entry, len), at(before_decrement, len)) + 1);
      at(loop(0).entry, buf) + (at(loop(0).entry, len) - len) == at(loop(0).entry, buf) + zlib_prefix_count(at(loop(0).entry, len), len);
     };
     have len <= old(len) by close() using { len <= at(before_decrement, len); at(before_decrement, len) <= old(len); old(len) <= 2147483647u64; };
     have to_integer(old(len) - at(before_decrement, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(old(len), at(before_decrement, len)));
      have to_integer(old(len)) <= 2147483647 by close() using { old(len) <= 2147483647u64; };
      have 0 <= to_integer(at(before_decrement, len)) by close();
      rewrite(to_integer(old(len) - at(before_decrement, len)), to_integer(old(len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(old(len)), 2147483647, to_integer(at(before_decrement, len)), 0));
      close();
     }
     have to_integer(old(len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(old(len), len));
      have to_integer(old(len)) <= 2147483647 by close() using { old(len) <= 2147483647u64; };
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(old(len) - len), to_integer(old(len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(old(len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_observation(old(len), at(before_decrement, len)));
     apply(zlib_full_prefix_observation(old(len), len));
     apply(zlib_full_prefix_pointer(old(buf), old(len), at(before_decrement, len))); apply(zlib_full_prefix_pointer(old(buf), old(len), len));
     have to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len)) + 1) by close();
     apply(zlib_full_chunk_bound(old(len), at(before_decrement, len), 1u64));
     have defined(zlib_prefix_count(old(len), at(before_decrement, len)) + 1) by close();
     apply(click::integer::uint8_pointer_add_associate_int32(old(buf), zlib_prefix_count(old(len), at(before_decrement, len)), 1));
     have buf == old(buf) + (old(len) - len) by close() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
      old(buf) + (old(len) - at(before_decrement, len)) == old(buf) + zlib_prefix_count(old(len), at(before_decrement, len));
      old(buf) + zlib_prefix_count(old(len), at(before_decrement, len)) + 1 == old(buf) + (zlib_prefix_count(old(len), at(before_decrement, len)) + 1);
      to_integer(zlib_prefix_count(old(len), len)) == to_integer(zlib_prefix_count(old(len), at(before_decrement, len)) + 1);
      old(buf) + (old(len) - len) == old(buf) + zlib_prefix_count(old(len), len);
     };
     have len <= 9223372036854775807u64 by close() using { len <= at(loop(0).entry, len); at(loop(0).entry, len) <= 15u64; };
   have separate(statement(6).statement(0).statement(1).footprint, memory(at(before_decrement, buf)[0u64..at(before_decrement, len)])) by close();
   have viewable(memory(at(before_decrement, buf)[0u64..at(before_decrement, len)])) by {
    preserve(memory(at(before_decrement, buf)[0u64..at(before_decrement, len)]), statement(6).statement(0).statement(1));
   }
   have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by close();
   have len == (at(before_decrement, len) - 1u64);
   have len <= at(before_decrement, len) - 1u64 by close();
   have len <= 15u64 by {
    have to_integer(len) <= to_integer(at(before_decrement, len)) by close() using {
     to_integer(len) == at(before_decrement, to_integer(len)) - 1;
    };
    apply(integer::uint64_to_integer_less_equal_implies_less_equal(len, at(before_decrement, len)));
    apply(integer::uint64_less_equal_transitive(len, at(before_decrement, len), 15u64));
   }
   have len <= 9223372036854775807u64;
   have contains(
    memory(at(before_decrement, buf)[0u64..at(before_decrement, len)]),
    memory(at(before_decrement, buf)[1u64..at(before_decrement, len)])
   ) by {
    apply(click::separation::contains_subrange(at(before_decrement, buf), 0u64, at(before_decrement, len), 1u64, at(before_decrement, len)));
   }
   have contains(
    memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]), memory(buf[0u64..len])
   ) by {
    rewrite(buf, at(before_decrement, buf) + 1u64);
    rewrite(len, at(before_decrement, len) - 1u64);
    apply(click::separation::contains_rebase(at(before_decrement, buf), 1u64, at(before_decrement, len)));
   }
   apply(click::separation::contains_trans(
    memory(at(before_decrement, buf)[0u64..at(before_decrement, len)]),
    memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]),
    memory(buf[0u64..len])
   ));
   apply(click::separation::viewable_restrict(memory(at(before_decrement, buf)[0u64..at(before_decrement, len)]), memory(buf[0u64..len])));

     have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
     have to_integer(len) < at(before_decrement, to_integer(len)) by close() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
    }
   }
  }
 mark short_raw;
 if adler >= 65521u64 {
  have 65521u64 <= adler by { close(); }
  have adler <= 131041u64 by close() using { adler <= 69345u64; };
  apply(zlib_reduce_once_above(adler));
  step_until(assignment(adler, 4).entry); step();
  have to_integer(adler) == at(short_raw, to_integer(adler % 65521u64)) by close();
 
 step_until(assignment(sum2, 4).entry); step();
 have sum2 == at(short_raw, sum2 % 65521u64) by close();
 have adler == at(short_raw, adler % 65521u64);
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using { adler == at(short_raw, adler % 65521u64); sum2 == at(short_raw, sum2 % 65521u64); at(short_raw, to_integer((adler % 65521u64) | ((sum2 % 65521u64) << 16))) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))); };
 step_until(function.exit); close();

 } else {
  have adler < 65521u64 by { close(); }
  apply(zlib_reduce_once_below(adler));
  step_until(assignment(sum2, 4).entry);
  have to_integer(adler) == at(short_raw, to_integer(adler % 65521u64)) by close();
 
 step_until(assignment(sum2, 4).entry); step();
 have sum2 == at(short_raw, sum2 % 65521u64) by close();
 have adler == at(short_raw, adler % 65521u64);
 have to_integer(adler | (sum2 << 16)) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using { adler == at(short_raw, adler % 65521u64); sum2 == at(short_raw, sum2 % 65521u64); at(short_raw, to_integer((adler % 65521u64) | ((sum2 % 65521u64) << 16))) == adler_spec_checksum(old(buf), old(len as uint32 as int32), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))); };
 step_until(function.exit); close();

 }
  } else {
   have 16u64 <= len by close() using { not (len <= 15u64); len <= 9223372036854775807u64; };
apply(zlib_seed_bounds(adler));
 have viewable(buf[0u64..len]) by close();
 unfold(zlib_seed_a(adler)); unfold(zlib_seed_b(adler));
 step_until(loop(1).entry);
 // Each outer head describes the reduced checksum of the completed prefix.
 loop {
  decreases to_integer(len);
  invariant forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
  invariant 0 <= to_integer(zlib_seed_a(old(adler)));
  invariant to_integer(zlib_seed_a(old(adler))) <= 65520;
  invariant 0 <= to_integer(zlib_seed_b(old(adler)));
  invariant len <= old(len);
  invariant old(len) <= 9223372036854775807u64;
  invariant buf == old(buf) + (old(len) - len);
  invariant viewable(buf[0u64..len]);
  invariant adler <= 65520u64;
  invariant sum2 <= 65520u64;
  invariant to_integer(adler) == adler_spec_a_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))));
  invariant to_integer(sum2) == adler_spec_b_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
  initialize by {
   have to_integer(old(len) - len) == to_integer(0u64) by close();
   have adler == zlib_seed_a(old(adler)) by close();
   have sum2 == zlib_seed_b(old(adler)) by close();
   have adler <= 65520u64 by close();
   have sum2 <= 65520u64 by close();
   have 0 <= to_integer(adler); have to_integer(adler) <= 18446744073709551615; have 0 <= to_integer(sum2); have to_integer(sum2) <= 18446744073709551615;
   have to_integer(adler) <= to_integer(65520u64);
   have to_integer(sum2) <= to_integer(65520u64);
   apply(adler_spec_empty_u64(old(buf), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
   have to_integer(adler) == adler_spec_a_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler)))) by { rewrite(to_integer(old(len) - len), to_integer(0u64)); rewrite(adler, zlib_seed_a(old(adler))); rewrite(adler_spec_a_u64(old(buf), 0u64, to_integer(zlib_seed_a(old(adler)))), to_integer(zlib_seed_a(old(adler)))); close(); }
   have to_integer(sum2) == adler_spec_b_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by { rewrite(to_integer(old(len) - len), to_integer(0u64)); rewrite(sum2, zlib_seed_b(old(adler))); rewrite(adler_spec_b_u64(old(buf), 0u64, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))), to_integer(zlib_seed_b(old(adler)))); close(); }
   close();
  }
  maintain by {
   have 5552u64 <= len by close();
   have len <= 9223372036854775807u64 by close() using { len <= old(len); old(len) <= 9223372036854775807u64; };
   have viewable(buf[0u64..5552u64]) by close();
   mark batch_entry;
   step(); step();
   step_until(loop(2).entry);
   loop {
    decreases to_integer(n);
    invariant 1u32 <= n;
    invariant n <= 347u32;
    invariant len == at(loop(2).entry, len);
    invariant to_integer(len) <= to_integer(old(len) - 5552u64);
    invariant len <= 9223372036854770255u64;
    invariant len <= old(len);
    invariant to_integer(5552u64) <= to_integer(old(len) - len);
    invariant 5552u64 <= old(len);
    invariant old(len) <= 9223372036854775807u64;
    invariant at(loop(2).entry, buf) == old(buf) + (old(len) - len - 5552u64);

    invariant at(loop(2).entry, len) <= 9223372036854775807u64;
    invariant at(loop(2).entry, adler) <= 65520u64;
    invariant at(loop(2).entry, sum2) <= 65520u64;
    invariant buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    invariant viewable(buf[0u64..16u64 * n as uint64]);
    // Preserve the pending batch and every byte following it.
    invariant viewable(buf[0u64..16u64 * n as uint64 + len]);
    invariant to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n));
    invariant to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n));
    invariant to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n));
    invariant to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n));
    initialize by {
     have len <= 9223372036854775807u64 by close() using {
      at(batch_entry, len) <= 9223372036854775807u64;
      5552u64 <= at(batch_entry, len);
      to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
     };
     have 5552u64 <= old(len) by close() using { 5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); };
     have to_integer(len) <= to_integer(old(len) - 5552u64) by close() using {
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); old(len) <= 9223372036854775807u64;
      to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
     };
     have len <= old(len) by close() using { to_integer(len) <= to_integer(old(len) - 5552u64); 5552u64 <= old(len); old(len) <= 9223372036854775807u64; };
     have to_integer(5552u64) <= to_integer(old(len) - len) by close() using { len <= old(len); to_integer(len) <= to_integer(old(len) - 5552u64); 5552u64 <= old(len); old(len) <= 9223372036854775807u64; };
     have to_integer(old(len) - len - 5552u64) == to_integer(old(len) - at(batch_entry, len)) by close() using {
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= old(len); old(len) <= 9223372036854775807u64;
      to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
     };
     have buf == old(buf) + (old(len) - len - 5552u64) by close() using {
      buf == old(buf) + (old(len) - at(batch_entry, len));
      to_integer(old(len) - len - 5552u64) == to_integer(old(len) - at(batch_entry, len));
     };
     have to_integer(5552u64) <= to_integer(at(batch_entry, len)) by close() using { 5552u64 <= at(batch_entry, len); };
     apply(click::integer::uint64_subtract_to_integer(at(batch_entry, len), 5552u64));
     have to_integer(at(batch_entry, len) - 5552u64) <= 9223372036854770255 by close() using {
      to_integer(at(batch_entry, len) - 5552u64) == to_integer(at(batch_entry, len)) - to_integer(5552u64);
      at(batch_entry, len) <= 9223372036854775807u64;
     };
     have len <= 9223372036854770255u64 by close() using {
      to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
      to_integer(at(batch_entry, len) - 5552u64) <= 9223372036854770255;
     };
     have n == 347u32 by close();
     have len == at(loop(2).entry, len) by close();
     have buf == at(loop(2).entry, buf) by close();
     have adler == at(loop(2).entry, adler) by close();
     have sum2 == at(loop(2).entry, sum2) by close();
     have at(loop(2).entry, len) <= 9223372036854775807u64 by {
      rewrite(at(loop(2).entry, len), len);
      close() using { len <= 9223372036854775807u64; };
     }
     have at(loop(2).entry, adler) <= 65520u64 by {
      rewrite(at(loop(2).entry, adler), adler);
      close() using { adler <= 65520u64; };
     }
     have at(loop(2).entry, sum2) <= 65520u64 by {
      rewrite(at(loop(2).entry, sum2), sum2);
      close() using { sum2 <= 65520u64; };
     }
     have viewable(buf[0u64..5552u64]) by {
      have at(statement(7).statement(1).entry, viewable(buf[0u64..5552u64])) by { close(); }
      have separate(statement(7).statement(1).footprint, memory(buf[0u64..5552u64])) by { close(); }
      preserve(memory(buf[0u64..5552u64]), statement(7).statement(1));
     }
     have viewable(buf[0u64..16u64 * n as uint64]) by close();
     have to_integer(16u64 * n as uint64 + len) == to_integer(at(batch_entry, len)) by close() using {
      n == 347u32; to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
      5552u64 <= at(batch_entry, len); at(batch_entry, len) <= 9223372036854775807u64;
     };
     have to_integer(16u64 * n as uint64 + len) <= to_integer(at(batch_entry, len)) by close() using { to_integer(16u64 * n as uint64 + len) == to_integer(at(batch_entry, len)); };
     have to_integer(16u64 * n as uint64 + len) <= to_integer(9223372036854775807u64) by close() using {
      to_integer(16u64 * n as uint64 + len) == to_integer(at(batch_entry, len));
      at(batch_entry, len) <= 9223372036854775807u64;
      n == 347u32; len <= 9223372036854770255u64;
     };
     have 16u64 * n as uint64 + len <= 9223372036854775807u64 by close() using {
      n == 347u32;
      len <= 9223372036854770255u64;
     };
     have buf == at(batch_entry, buf) by close();
     have at(statement(7).statement(1).entry, viewable(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)]))) by close();
     have separate(statement(7).statement(1).footprint, memory(at(batch_entry, buf)[0u64..at(batch_entry, len)])) by close();
     have viewable(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)])) by {
      preserve(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)]), statement(7).statement(1));
     }
     have contains(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)]), memory(at(batch_entry, buf)[0u64..16u64 * n as uint64 + len])) by {
      rewrite(to_integer(16u64 * n as uint64 + len), to_integer(at(batch_entry, len)));
      apply(click::separation::contains_refl(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)])));
     }
     apply(click::separation::viewable_restrict(memory(at(batch_entry, buf)[0u64..at(batch_entry, len)]), memory(at(batch_entry, buf)[0u64..16u64 * n as uint64 + len])));
     have viewable(buf[0u64..16u64 * n as uint64 + len]) by {
      rewrite(buf, at(batch_entry, buf));
      close();
     }
     apply(zlib_batch_prefix_initial());
     have zlib_batch_count(n) == 0 by close();
     have to_integer(adler) <= to_integer(65520u64);
     have to_integer(sum2) <= to_integer(65520u64);
     apply(adler_sum_empty(at(loop(2).entry, buf), 0));
     have buf == at(loop(2).entry, buf) + zlib_batch_count(n) by { rewrite(zlib_batch_count(n), 0); close(); }
     have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n), 0); rewrite(adler_byte_sum(at(loop(2).entry, buf), 0), 0); close();
     }
     have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)) by {
      rewrite(zlib_batch_count(n), 0); rewrite(adler_weighted_sum(at(loop(2).entry, buf), 0, 0), 0); close();
     }
     have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n), 0); close() using { to_integer(adler) <= 65520; }; }
     have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n)) by { rewrite(zlib_batch_count(n), 0); close() using { to_integer(sum2) <= 65520; }; }
     close();
    }
    maintain by {
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     apply(zlib_batch_remaining_limit(n));
     apply(zlib_batch_nonempty_remaining(n));
     have to_integer(16u64) <= to_integer(16u64 * n as uint64) by { unfold(zlib_batch_remaining(n)); close(); }
     have to_integer(16u64 * n as uint64) <= to_integer(5552u64) by { unfold(zlib_batch_remaining(n)); close(); }
     have to_integer(1u64) <= to_integer(16u64 * n as uint64) by close() using { to_integer(16u64) <= to_integer(16u64 * n as uint64); };
     have to_integer(16u64 * n as uint64) <= to_integer(9223372036854775807u64) by close() using { to_integer(16u64 * n as uint64) <= to_integer(5552u64); };
     apply(zlib_batch_cursor(at(loop(2).entry, buf), n));
     have buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n)) by close() using {
      buf == at(loop(2).entry, buf) + zlib_batch_count(n);
      at(loop(2).entry, buf) + zlib_batch_count(n) == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
     };
     have to_integer(5552u64 - zlib_batch_remaining(n)) < to_integer(5552u64) by close() using { 16u64 <= zlib_batch_remaining(n); zlib_batch_remaining(n) <= 5552u64; };
     

     have to_integer(len) <= to_integer(old(len) - 5552u64) by close();
     apply(zlib_full_stream_batch_read_bound_u64(old(len), len, n));
     have to_integer(old(len) - len - 5552u64) <= to_integer(9223372036854775807u64) by close() using { len <= old(len); to_integer(5552u64) <= to_integer(old(len) - len); old(len) <= 9223372036854775807u64; };
     have to_integer(5552u64 - zlib_batch_remaining(n)) <= to_integer(5552u64) by close() using { zlib_batch_remaining(n) <= 5552u64; };
     have to_integer((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(9223372036854775807u64) by close() using {
      to_integer((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n))) <= to_integer(old(len) - 16u64);
      len <= old(len); to_integer(5552u64) <= to_integer(old(len) - len); 5552u64 <= old(len); old(len) <= 9223372036854775807u64;
      zlib_batch_remaining(n) <= 5552u64;
     };
     have to_integer(old(len) - len - 5552u64) <= to_integer(9223372036854775807u64);
     have to_integer(5552u64 - zlib_batch_remaining(n)) <= to_integer(5552u64);
     have to_integer(old(len) - len - 5552u64) + to_integer(5552u64 - zlib_batch_remaining(n)) <= 18446744073709551615 by {
      apply(integer::add_le(to_integer(old(len) - len - 5552u64), 9223372036854775807, to_integer(5552u64 - zlib_batch_remaining(n)), 5552));
      apply(integer::le_transitive(to_integer(old(len) - len - 5552u64) + to_integer(5552u64 - zlib_batch_remaining(n)), 9223372036854775807 + 5552, 18446744073709551615));
     }
     apply(zlib_full_native_cursor_join_u64(old(buf), old(len) - len - 5552u64, 5552u64 - zlib_batch_remaining(n)));
     have buf == old(buf) + ((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n))) by close() using {
      buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
      at(loop(2).entry, buf) == old(buf) + (old(len) - len - 5552u64);
      old(buf) + (old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)) == old(buf) + ((old(len) - len - 5552u64) + (5552u64 - zlib_batch_remaining(n)));
     };
     have old(len) <= 9223372036854775807u64 by close() using { old(len) <= 9223372036854775807u64; };
     have 16u64 <= 16u64 * n as uint64 + len by close() using {
      1u32 <= n; n <= 347u32; len <= 9223372036854770255u64;
     };
     mark before_block;
   step_until(assignment(adler, 5).entry);
   apply(zlib_batch_read_bound(n, 0u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 0u64));
   apply(zlib_batch_lane_defined(n, 0)); apply(zlib_batch_lane(n, 0));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 0));
   have buf[0] == at(loop(2).entry, buf)[zlib_batch_count(n)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[0] == at(loop(2).entry, buf)[zlib_batch_count(n) + 0];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), zlib_batch_count(n), adler, sum2, buf[0], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   have viewable(buf[0u64..1u64]) by close();
   mark byte_0;
   step();
   step_until(assignment(sum2, 5).entry);
   step();
   have separate(loop(2).statement(0).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(0).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_0, adler + buf[0] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_0, adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 1, zlib_batch_count(n) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_0, adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 1);
   };
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1)) by close();
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1), (zlib_batch_count(n) + 1)) by close();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1)) by close();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1)) by close();
   step_until(assignment(adler, 6).entry);
   apply(zlib_batch_read_bound(n, 1u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 1u64));
   apply(zlib_batch_lane_defined(n, 1)); apply(zlib_batch_lane(n, 1));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 1));
   have buf[1] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 1)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[1] == at(loop(2).entry, buf)[zlib_batch_count(n) + 1];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 1), adler, sum2, buf[1], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_1;
   step();
   step_until(assignment(sum2, 6).entry);
   step();
   have separate(loop(2).statement(2).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(2).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_1, adler + buf[1] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_1, adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 1) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 1) + 1, (zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_1, adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 1) + 1);
   };
   have zlib_batch_count(n) + 2 == (zlib_batch_count(n) + 1) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2)) by { rewrite(zlib_batch_count(n) + 2, (zlib_batch_count(n) + 1) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2), (zlib_batch_count(n) + 2)) by { rewrite(zlib_batch_count(n) + 2, (zlib_batch_count(n) + 1) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2)) by { rewrite(zlib_batch_count(n) + 2, (zlib_batch_count(n) + 1) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2)) by { rewrite(zlib_batch_count(n) + 2, (zlib_batch_count(n) + 1) + 1); close(); }
   step_until(assignment(adler, 7).entry);
   apply(zlib_batch_read_bound(n, 2u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 2u64));
   apply(zlib_batch_lane_defined(n, 2)); apply(zlib_batch_lane(n, 2));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 2));
   have buf[2] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 2)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[2] == at(loop(2).entry, buf)[zlib_batch_count(n) + 2];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 2), adler, sum2, buf[2], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_2;
   step();
   step_until(assignment(sum2, 7).entry);
   step();
   have separate(loop(2).statement(5).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(5).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_2, adler + buf[2] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_2, adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 2) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 2) + 1, (zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_2, adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 2) + 1);
   };
   have zlib_batch_count(n) + 3 == (zlib_batch_count(n) + 2) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3)) by { rewrite(zlib_batch_count(n) + 3, (zlib_batch_count(n) + 2) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3), (zlib_batch_count(n) + 3)) by { rewrite(zlib_batch_count(n) + 3, (zlib_batch_count(n) + 2) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3)) by { rewrite(zlib_batch_count(n) + 3, (zlib_batch_count(n) + 2) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3)) by { rewrite(zlib_batch_count(n) + 3, (zlib_batch_count(n) + 2) + 1); close(); }
   step_until(assignment(adler, 8).entry);
   apply(zlib_batch_read_bound(n, 3u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 3u64));
   apply(zlib_batch_lane_defined(n, 3)); apply(zlib_batch_lane(n, 3));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 3));
   have buf[3] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 3)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[3] == at(loop(2).entry, buf)[zlib_batch_count(n) + 3];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 3), adler, sum2, buf[3], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_3;
   step();
   step_until(assignment(sum2, 8).entry);
   step();
   have separate(loop(2).statement(7).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(7).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_3, adler + buf[3] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_3, adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 3) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 3) + 1, (zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_3, adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 3) + 1);
   };
   have zlib_batch_count(n) + 4 == (zlib_batch_count(n) + 3) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4)) by { rewrite(zlib_batch_count(n) + 4, (zlib_batch_count(n) + 3) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4), (zlib_batch_count(n) + 4)) by { rewrite(zlib_batch_count(n) + 4, (zlib_batch_count(n) + 3) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4)) by { rewrite(zlib_batch_count(n) + 4, (zlib_batch_count(n) + 3) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4)) by { rewrite(zlib_batch_count(n) + 4, (zlib_batch_count(n) + 3) + 1); close(); }
   step_until(assignment(adler, 9).entry);
   apply(zlib_batch_read_bound(n, 4u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 4u64));
   apply(zlib_batch_lane_defined(n, 4)); apply(zlib_batch_lane(n, 4));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 4));
   have buf[4] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 4)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[4] == at(loop(2).entry, buf)[zlib_batch_count(n) + 4];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 4), adler, sum2, buf[4], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_4;
   step();
   step_until(assignment(sum2, 9).entry);
   step();
   have separate(loop(2).statement(11).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(11).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_4, adler + buf[4] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_4, adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 4) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 4) + 1, (zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_4, adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 4) + 1);
   };
   have zlib_batch_count(n) + 5 == (zlib_batch_count(n) + 4) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5)) by { rewrite(zlib_batch_count(n) + 5, (zlib_batch_count(n) + 4) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5), (zlib_batch_count(n) + 5)) by { rewrite(zlib_batch_count(n) + 5, (zlib_batch_count(n) + 4) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5)) by { rewrite(zlib_batch_count(n) + 5, (zlib_batch_count(n) + 4) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5)) by { rewrite(zlib_batch_count(n) + 5, (zlib_batch_count(n) + 4) + 1); close(); }
   step_until(assignment(adler, 10).entry);
   apply(zlib_batch_read_bound(n, 5u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 5u64));
   apply(zlib_batch_lane_defined(n, 5)); apply(zlib_batch_lane(n, 5));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 5));
   have buf[5] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 5)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[5] == at(loop(2).entry, buf)[zlib_batch_count(n) + 5];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 5), adler, sum2, buf[5], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_5;
   step();
   step_until(assignment(sum2, 10).entry);
   step();
   have separate(loop(2).statement(13).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(13).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_5, adler + buf[5] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_5, adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 5) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 5) + 1, (zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_5, adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 5) + 1);
   };
   have zlib_batch_count(n) + 6 == (zlib_batch_count(n) + 5) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6)) by { rewrite(zlib_batch_count(n) + 6, (zlib_batch_count(n) + 5) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6), (zlib_batch_count(n) + 6)) by { rewrite(zlib_batch_count(n) + 6, (zlib_batch_count(n) + 5) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6)) by { rewrite(zlib_batch_count(n) + 6, (zlib_batch_count(n) + 5) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6)) by { rewrite(zlib_batch_count(n) + 6, (zlib_batch_count(n) + 5) + 1); close(); }
   step_until(assignment(adler, 11).entry);
   apply(zlib_batch_read_bound(n, 6u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 6u64));
   apply(zlib_batch_lane_defined(n, 6)); apply(zlib_batch_lane(n, 6));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 6));
   have buf[6] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 6)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[6] == at(loop(2).entry, buf)[zlib_batch_count(n) + 6];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 6), adler, sum2, buf[6], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_6;
   step();
   step_until(assignment(sum2, 11).entry);
   step();
   have separate(loop(2).statement(16).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(16).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_6, adler + buf[6] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_6, adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 6) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 6) + 1, (zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_6, adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 6) + 1);
   };
   have zlib_batch_count(n) + 7 == (zlib_batch_count(n) + 6) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7)) by { rewrite(zlib_batch_count(n) + 7, (zlib_batch_count(n) + 6) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7), (zlib_batch_count(n) + 7)) by { rewrite(zlib_batch_count(n) + 7, (zlib_batch_count(n) + 6) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7)) by { rewrite(zlib_batch_count(n) + 7, (zlib_batch_count(n) + 6) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7)) by { rewrite(zlib_batch_count(n) + 7, (zlib_batch_count(n) + 6) + 1); close(); }
   step_until(assignment(adler, 12).entry);
   apply(zlib_batch_read_bound(n, 7u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 7u64));
   apply(zlib_batch_lane_defined(n, 7)); apply(zlib_batch_lane(n, 7));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 7));
   have buf[7] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 7)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[7] == at(loop(2).entry, buf)[zlib_batch_count(n) + 7];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 7), adler, sum2, buf[7], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_7;
   step();
   step_until(assignment(sum2, 12).entry);
   step();
   have separate(loop(2).statement(18).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(18).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_7, adler + buf[7] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_7, adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 7) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 7) + 1, (zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_7, adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 7) + 1);
   };
   have zlib_batch_count(n) + 8 == (zlib_batch_count(n) + 7) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8)) by { rewrite(zlib_batch_count(n) + 8, (zlib_batch_count(n) + 7) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8), (zlib_batch_count(n) + 8)) by { rewrite(zlib_batch_count(n) + 8, (zlib_batch_count(n) + 7) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8)) by { rewrite(zlib_batch_count(n) + 8, (zlib_batch_count(n) + 7) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8)) by { rewrite(zlib_batch_count(n) + 8, (zlib_batch_count(n) + 7) + 1); close(); }
   step_until(assignment(adler, 13).entry);
   apply(zlib_batch_read_bound(n, 8u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 8u64));
   apply(zlib_batch_lane_defined(n, 8)); apply(zlib_batch_lane(n, 8));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 8));
   have buf[8] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 8)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[8] == at(loop(2).entry, buf)[zlib_batch_count(n) + 8];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 8), adler, sum2, buf[8], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_8;
   step();
   step_until(assignment(sum2, 13).entry);
   step();
   have separate(loop(2).statement(23).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(23).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_8, adler + buf[8] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_8, adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 8) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 8) + 1, (zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_8, adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 8) + 1);
   };
   have zlib_batch_count(n) + 9 == (zlib_batch_count(n) + 8) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9)) by { rewrite(zlib_batch_count(n) + 9, (zlib_batch_count(n) + 8) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9), (zlib_batch_count(n) + 9)) by { rewrite(zlib_batch_count(n) + 9, (zlib_batch_count(n) + 8) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9)) by { rewrite(zlib_batch_count(n) + 9, (zlib_batch_count(n) + 8) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9)) by { rewrite(zlib_batch_count(n) + 9, (zlib_batch_count(n) + 8) + 1); close(); }
   step_until(assignment(adler, 14).entry);
   apply(zlib_batch_read_bound(n, 9u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 9u64));
   apply(zlib_batch_lane_defined(n, 9)); apply(zlib_batch_lane(n, 9));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 9));
   have buf[9] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 9)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[9] == at(loop(2).entry, buf)[zlib_batch_count(n) + 9];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 9), adler, sum2, buf[9], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_9;
   step();
   step_until(assignment(sum2, 14).entry);
   step();
   have separate(loop(2).statement(25).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(25).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_9, adler + buf[9] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_9, adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 9) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 9) + 1, (zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_9, adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 9) + 1);
   };
   have zlib_batch_count(n) + 10 == (zlib_batch_count(n) + 9) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10)) by { rewrite(zlib_batch_count(n) + 10, (zlib_batch_count(n) + 9) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10), (zlib_batch_count(n) + 10)) by { rewrite(zlib_batch_count(n) + 10, (zlib_batch_count(n) + 9) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10)) by { rewrite(zlib_batch_count(n) + 10, (zlib_batch_count(n) + 9) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10)) by { rewrite(zlib_batch_count(n) + 10, (zlib_batch_count(n) + 9) + 1); close(); }
   step_until(assignment(adler, 15).entry);
   apply(zlib_batch_read_bound(n, 10u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 10u64));
   apply(zlib_batch_lane_defined(n, 10)); apply(zlib_batch_lane(n, 10));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 10));
   have buf[10] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 10)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[10] == at(loop(2).entry, buf)[zlib_batch_count(n) + 10];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 10), adler, sum2, buf[10], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_10;
   step();
   step_until(assignment(sum2, 15).entry);
   step();
   have separate(loop(2).statement(28).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(28).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_10, adler + buf[10] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_10, adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 10) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 10) + 1, (zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_10, adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 10) + 1);
   };
   have zlib_batch_count(n) + 11 == (zlib_batch_count(n) + 10) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11)) by { rewrite(zlib_batch_count(n) + 11, (zlib_batch_count(n) + 10) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11), (zlib_batch_count(n) + 11)) by { rewrite(zlib_batch_count(n) + 11, (zlib_batch_count(n) + 10) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11)) by { rewrite(zlib_batch_count(n) + 11, (zlib_batch_count(n) + 10) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11)) by { rewrite(zlib_batch_count(n) + 11, (zlib_batch_count(n) + 10) + 1); close(); }
   step_until(assignment(adler, 16).entry);
   apply(zlib_batch_read_bound(n, 11u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 11u64));
   apply(zlib_batch_lane_defined(n, 11)); apply(zlib_batch_lane(n, 11));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 11));
   have buf[11] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 11)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[11] == at(loop(2).entry, buf)[zlib_batch_count(n) + 11];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 11), adler, sum2, buf[11], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_11;
   step();
   step_until(assignment(sum2, 16).entry);
   step();
   have separate(loop(2).statement(30).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(30).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_11, adler + buf[11] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_11, adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 11) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 11) + 1, (zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_11, adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 11) + 1);
   };
   have zlib_batch_count(n) + 12 == (zlib_batch_count(n) + 11) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12)) by { rewrite(zlib_batch_count(n) + 12, (zlib_batch_count(n) + 11) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12), (zlib_batch_count(n) + 12)) by { rewrite(zlib_batch_count(n) + 12, (zlib_batch_count(n) + 11) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12)) by { rewrite(zlib_batch_count(n) + 12, (zlib_batch_count(n) + 11) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12)) by { rewrite(zlib_batch_count(n) + 12, (zlib_batch_count(n) + 11) + 1); close(); }
   step_until(assignment(adler, 17).entry);
   apply(zlib_batch_read_bound(n, 12u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 12u64));
   apply(zlib_batch_lane_defined(n, 12)); apply(zlib_batch_lane(n, 12));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 12));
   have buf[12] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 12)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[12] == at(loop(2).entry, buf)[zlib_batch_count(n) + 12];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 12), adler, sum2, buf[12], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_12;
   step();
   step_until(assignment(sum2, 17).entry);
   step();
   have separate(loop(2).statement(34).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(34).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_12, adler + buf[12] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_12, adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 12) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 12) + 1, (zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_12, adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 12) + 1);
   };
   have zlib_batch_count(n) + 13 == (zlib_batch_count(n) + 12) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13)) by { rewrite(zlib_batch_count(n) + 13, (zlib_batch_count(n) + 12) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13), (zlib_batch_count(n) + 13)) by { rewrite(zlib_batch_count(n) + 13, (zlib_batch_count(n) + 12) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13)) by { rewrite(zlib_batch_count(n) + 13, (zlib_batch_count(n) + 12) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13)) by { rewrite(zlib_batch_count(n) + 13, (zlib_batch_count(n) + 12) + 1); close(); }
   step_until(assignment(adler, 18).entry);
   apply(zlib_batch_read_bound(n, 13u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 13u64));
   apply(zlib_batch_lane_defined(n, 13)); apply(zlib_batch_lane(n, 13));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 13));
   have buf[13] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 13)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[13] == at(loop(2).entry, buf)[zlib_batch_count(n) + 13];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 13), adler, sum2, buf[13], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_13;
   step();
   step_until(assignment(sum2, 18).entry);
   step();
   have separate(loop(2).statement(36).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(36).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_13, adler + buf[13] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_13, adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 13) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 13) + 1, (zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_13, adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 13) + 1);
   };
   have zlib_batch_count(n) + 14 == (zlib_batch_count(n) + 13) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14)) by { rewrite(zlib_batch_count(n) + 14, (zlib_batch_count(n) + 13) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14), (zlib_batch_count(n) + 14)) by { rewrite(zlib_batch_count(n) + 14, (zlib_batch_count(n) + 13) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14)) by { rewrite(zlib_batch_count(n) + 14, (zlib_batch_count(n) + 13) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14)) by { rewrite(zlib_batch_count(n) + 14, (zlib_batch_count(n) + 13) + 1); close(); }
   step_until(assignment(adler, 19).entry);
   apply(zlib_batch_read_bound(n, 14u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 14u64));
   apply(zlib_batch_lane_defined(n, 14)); apply(zlib_batch_lane(n, 14));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 14));
   have buf[14] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 14)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[14] == at(loop(2).entry, buf)[zlib_batch_count(n) + 14];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 14), adler, sum2, buf[14], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_14;
   step();
   step_until(assignment(sum2, 19).entry);
   step();
   have separate(loop(2).statement(39).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(39).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_14, adler + buf[14] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_14, adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 14) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 14) + 1, (zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_14, adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 14) + 1);
   };
   have zlib_batch_count(n) + 15 == (zlib_batch_count(n) + 14) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15)) by { rewrite(zlib_batch_count(n) + 15, (zlib_batch_count(n) + 14) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15), (zlib_batch_count(n) + 15)) by { rewrite(zlib_batch_count(n) + 15, (zlib_batch_count(n) + 14) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15)) by { rewrite(zlib_batch_count(n) + 15, (zlib_batch_count(n) + 14) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15)) by { rewrite(zlib_batch_count(n) + 15, (zlib_batch_count(n) + 14) + 1); close(); }
   step_until(assignment(adler, 20).entry);
   apply(zlib_batch_read_bound(n, 15u64));
   apply(zlib_full_stream_batch_lane_bound_u64(old(len), len, n, 15u64));
   apply(zlib_batch_lane_defined(n, 15)); apply(zlib_batch_lane(n, 15));
   apply(zlib_batch_byte_lane(at(loop(2).entry, buf), n, 15));
   have buf[15] == at(loop(2).entry, buf)[(zlib_batch_count(n) + 15)] by close() using {
    buf == at(loop(2).entry, buf) + zlib_batch_count(n);
    (at(loop(2).entry, buf) + zlib_batch_count(n))[15] == at(loop(2).entry, buf)[zlib_batch_count(n) + 15];
   };
   apply(zlib_seeded_component_step(at(loop(2).entry, buf), (zlib_batch_count(n) + 15), adler, sum2, buf[15], at(loop(2).entry, adler), at(loop(2).entry, sum2)));
   mark byte_15;
   step();
   step_until(assignment(sum2, 20).entry);
   step();
   have separate(loop(2).statement(41).statement(1).assignment(sum2, 0).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
   have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), loop(2).statement(41).statement(1).assignment(sum2, 0)); }
   have to_integer(adler) == to_integer(at(byte_15, adler + buf[15] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_15, adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 15) + 1) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 15) + 1, (zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_15, adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 15) + 1);
   };
   have zlib_batch_count(n) + 16 == (zlib_batch_count(n) + 15) + 1 by close();
   have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 16)) by { rewrite(zlib_batch_count(n) + 16, (zlib_batch_count(n) + 15) + 1); close(); }
   have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer((zlib_batch_count(n) + 16)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), (zlib_batch_count(n) + 16), (zlib_batch_count(n) + 16)) by { rewrite(zlib_batch_count(n) + 16, (zlib_batch_count(n) + 15) + 1); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_batch_count(n) + 16)) by { rewrite(zlib_batch_count(n) + 16, (zlib_batch_count(n) + 15) + 1); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_batch_count(n) + 16)) by { rewrite(zlib_batch_count(n) + 16, (zlib_batch_count(n) + 15) + 1); close(); }

     apply(zlib_batch_prefix_step(n));
     apply(zlib_batch_prefix_limit(n));
     apply(zlib_batch_nonempty_prefix(n));
     have to_integer(zlib_batch_count(n)) + to_integer(16) >= -2147483648 by close() using { 0 <= to_integer(zlib_batch_count(n)); };
     have to_integer(zlib_batch_count(n)) + to_integer(16) <= 2147483647 by close() using { to_integer(zlib_batch_count(n)) <= 5552; };
     have defined(zlib_batch_count(n) + 16);
     have defined(zlib_batch_count(n) + 16) by close();
     step_until(assignment(buf, 1).entry);
     mark before_advance;
     step();
     have buf == at(before_advance, buf) + 16 by close();
     apply(click::integer::uint8_pointer_add_associate_int32(at(loop(2).entry, buf), zlib_batch_count(n), 16));
     have buf == at(loop(2).entry, buf) + zlib_batch_count(n - 1u32) by close() using {
      buf == at(before_advance, buf) + 16;
      at(before_advance, buf) == at(loop(2).entry, buf) + zlib_batch_count(n);
      at(loop(2).entry, buf) + zlib_batch_count(n) + 16 == at(loop(2).entry, buf) + (zlib_batch_count(n) + 16);
      to_integer(zlib_batch_count(n - 1u32)) == to_integer(zlib_batch_count(n) + 16);
     };
     have to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n - 1u32)) by close() using {
      to_integer(adler) == to_integer(at(loop(2).entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 16);
      to_integer(zlib_batch_count(n - 1u32)) == to_integer(zlib_batch_count(n) + 16);
     };
     have to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n - 1u32)) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n - 1u32), zlib_batch_count(n - 1u32)) by {
      have zlib_batch_count(n - 1u32) == (zlib_batch_count(n) + 16) as int32 by close() using {
       to_integer(zlib_batch_count(n - 1u32)) == to_integer(zlib_batch_count(n) + 16);
      };
      apply(zlib_canonical_weighted_sum_count_equal(at(loop(2).entry, buf), zlib_batch_count(n - 1u32), (zlib_batch_count(n) + 16) as int32));
      rewrite(adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n - 1u32), zlib_batch_count(n - 1u32)), adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 16, zlib_batch_count(n) + 16));
      rewrite(to_integer(zlib_batch_count(n - 1u32)), to_integer(zlib_batch_count(n) + 16));
      close() using { to_integer(sum2) == to_integer(at(loop(2).entry, sum2)) + to_integer(zlib_batch_count(n) + 16) * to_integer(at(loop(2).entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n) + 16, zlib_batch_count(n) + 16); };
     }
     step();
     have separate(statement(7).statement(2).region(1).footprint, memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by close();
     have viewable(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)])) by { preserve(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), statement(7).statement(2).region(1)); }
     have to_integer(n) == to_integer(at(before_advance, n) - 1u32) by close();
     have len == at(before_block, len) by close();
     apply(zlib_full_stream_capacity_step_u64(at(before_advance, n), len));
     have to_integer(16u64 * n as uint64 + len) == to_integer(at(before_block, 16u64 * n as uint64 + len) - 16u64) by close() using {
      to_integer(n) == to_integer(at(before_advance, n) - 1u32);
      len == at(before_block, len);
      to_integer(at(before_advance, 16u64 * (n - 1u32) as uint64) + len) == to_integer(at(before_advance, 16u64 * n as uint64) + len - 16u64);
     };
     have to_integer(16u64 * n as uint64 + len) <= to_integer(at(before_block, 16u64 * n as uint64 + len) - 16u64) by close() using {
      to_integer(16u64 * n as uint64 + len) == to_integer(at(before_block, 16u64 * n as uint64 + len) - 16u64);
     };
     have to_integer(16u64 * n as uint64 + len) <= to_integer(9223372036854775807u64) by close() using {
      to_integer(n) == to_integer(at(before_advance, n) - 1u32);
      to_integer(at(before_advance, 16u64 * (n - 1u32) as uint64) + len) <= to_integer(9223372036854775807u64);
     };
     have to_integer(16u64 * n as uint64 + len) <= to_integer(9223372036854775807u64) by close() using {
      to_integer(16u64 * n as uint64 + len) <= to_integer(9223372036854775807u64);
      n <= 347u32; len <= 9223372036854770255u64;
     };
     have buf == at(before_block, buf) + 16 by close();
     have to_integer(16u64) <= to_integer(at(before_block, 16u64 * n as uint64 + len)) by close() using {
      to_integer(16u64) <= to_integer(at(before_block, 16u64 * n as uint64));
      to_integer(at(before_block, 16u64 * n as uint64)) <= to_integer(5552u64);
      len <= 9223372036854770255u64;
      len == at(before_block, len);
     };

     apply(click::separation::contains_subrange(at(before_block, buf), 0u64, at(before_block, 16u64 * n as uint64 + len), 16u64, at(before_block, 16u64 * n as uint64 + len)));
     have contains(memory(at(before_block, buf)[16u64..at(before_block, 16u64 * n as uint64 + len)]), memory(buf[0u64..16u64 * n as uint64 + len])) by {
      rewrite(buf, at(before_block, buf) + 16);
      rewrite(to_integer(16u64 * n as uint64 + len), to_integer(at(before_block, 16u64 * n as uint64 + len) - 16u64));
      apply(click::separation::contains_rebase(at(before_block, buf), 16u64, at(before_block, 16u64 * n as uint64 + len)));
     }
     apply(click::separation::contains_trans(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), memory(at(before_block, buf)[16u64..at(before_block, 16u64 * n as uint64 + len)]), memory(buf[0u64..16u64 * n as uint64 + len])));
     apply(click::separation::viewable_restrict(memory(at(before_block, buf)[0u64..at(before_block, 16u64 * n as uint64 + len)]), memory(buf[0u64..16u64 * n as uint64 + len])));
     mark after_counter;
     if n == 0u32 {
      step();
      have viewable(buf[0u64..16u64 * n as uint64 + len]) by {
       close();
      }
     } else {
      step();
      apply(zlib_batch_positive(n));
      have n <= 347u32 by close();
      have len == at(loop(2).entry, len) by close();
      have at(loop(2).entry, len) <= 9223372036854775807u64 by close();
      apply(zlib_batch_remaining_limit(n));
      unfold(zlib_batch_remaining(n));
      have to_integer(16u64 * n as uint64) <= to_integer(5552u64) by close();
      have to_integer(16u64 * n as uint64) <= to_integer(9223372036854775807u64) by close() using { to_integer(16u64 * n as uint64) <= to_integer(5552u64); };
      apply(zlib_batch_cursor(at(loop(2).entry, buf), n));
      have buf == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n)) by close() using {
       buf == at(loop(2).entry, buf) + zlib_batch_count(n);
       at(loop(2).entry, buf) + zlib_batch_count(n) == at(loop(2).entry, buf) + (5552u64 - zlib_batch_remaining(n));
      };
      apply(zlib_batch_capacity_step(at(before_advance, n)));
      have to_integer(n) == to_integer(at(before_advance, n) - 1u32) by close();
      have to_integer(16u64 * n as uint64) == to_integer(at(before_advance, 16u64 * n as uint64) - 16u64) by close() using {
       to_integer(n) == to_integer(at(before_advance, n) - 1u32);
       to_integer(at(before_advance, 16u64 * (n - 1u32) as uint64)) == to_integer(at(before_advance, 16u64 * n as uint64 - 16u64));
      };
      have to_integer(16u64 * n as uint64) <= to_integer(at(before_block, 16u64 * n as uint64) - 16u64) by close() using {
       to_integer(16u64 * n as uint64) == to_integer(at(before_advance, 16u64 * n as uint64) - 16u64);
      };
      have buf == at(before_block, buf) + 16 by close();
      have 16u64 * n as uint64 <= 16u64 * n as uint64 + len by close() using {
       n <= 347u32; len <= 9223372036854770255u64;
      };
      have to_integer(16u64 * n as uint64) + to_integer(len) <= 18446744073709551615 by close() using {
       to_integer(16u64 * n as uint64) <= to_integer(5552u64);
       len <= 9223372036854770255u64;
      };
      apply(click::integer::uint64_add_to_integer(16u64 * n as uint64, len));
      have 0 <= to_integer(len) by close();
      have to_integer(16u64 * n as uint64) <= to_integer(16u64 * n as uint64 + len) by {
       rewrite(to_integer(16u64 * n as uint64 + len), to_integer(16u64 * n as uint64) + to_integer(len));
       close() using { 0 <= to_integer(len); };
      }
      apply(click::separation::contains_subrange(buf, 0u64, 16u64 * n as uint64 + len, 0u64, 16u64 * n as uint64));
      apply(click::separation::viewable_restrict(memory(buf[0u64..16u64 * n as uint64 + len]), memory(buf[0u64..16u64 * n as uint64])));
      have to_integer(zlib_batch_count(n)) == to_integer(at(before_advance, zlib_batch_count(n) + 16)) by close() using {
       to_integer(n) == to_integer(at(before_advance, n) - 1u32);
       to_integer(at(before_advance, zlib_batch_count(n - 1u32))) == to_integer(at(before_advance, zlib_batch_count(n) + 16));
      };
      have adler == at(before_advance, adler) by close();
      have sum2 == at(before_advance, sum2) by close();
      have to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n)) by close() using {
       adler == at(before_advance, adler);
       at(before_advance, to_integer(adler) <= 65520 + 255 * to_integer(zlib_batch_count(n) + 16));
       to_integer(zlib_batch_count(n)) == to_integer(at(before_advance, zlib_batch_count(n) + 16));
      };
      have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n)) by close() using {
       sum2 == at(before_advance, sum2);
       at(before_advance, to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_batch_count(n) + 16));
       to_integer(zlib_batch_count(n)) == to_integer(at(before_advance, zlib_batch_count(n) + 16));
      };
      have 0 <= to_integer(n); have to_integer(n) <= 4294967295;
      have to_integer(at(before_advance, n) - 1u32) == to_integer(at(before_advance, n)) - to_integer(1u32);
      have to_integer(n) == at(before_advance, to_integer(n)) - 1 by close() using {
       to_integer(n) == to_integer(at(before_advance, n) - 1u32);
       to_integer(at(before_advance, n) - 1u32) == to_integer(at(before_advance, n)) - to_integer(1u32);
      };
      have to_integer(n) < at(before_advance, to_integer(n)) by close() using {
       to_integer(n) == at(before_advance, to_integer(n)) - 1;
      };
      have viewable(buf[0u64..16u64 * n as uint64 + len]) by {
       close();
      }
     }
    }
   }
   have n == 0u32 by close();
   apply(zlib_batch_prefix_final());
   have zlib_batch_count(n) == 5552 by close();
   have to_integer(len) == to_integer(at(batch_entry, len) - 5552u64) by close();
   have to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), 5552) by close() using {
    to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), zlib_batch_count(n));
    zlib_batch_count(n) == 5552;
   };
   have to_integer(zlib_batch_count(n)) == 5552 by close() using { zlib_batch_count(n) == 5552; };
   have adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)) == adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552) by close() using { zlib_batch_count(n) == 5552; };
   have to_integer(sum2) == to_integer(at(batch_entry, sum2)) + 5552 * to_integer(at(batch_entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552) by {
    have to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)) == 5552 * to_integer(at(batch_entry, adler)) by { rewrite(to_integer(zlib_batch_count(n)), 5552); close(); }
    rewrite(5552 * to_integer(at(batch_entry, adler)), to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)));
    rewrite(adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552), adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)));
    close() using { to_integer(sum2) == to_integer(at(batch_entry, sum2)) + to_integer(zlib_batch_count(n)) * to_integer(at(batch_entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), zlib_batch_count(n), zlib_batch_count(n)); };
   }
   have at(batch_entry, len) <= old(len) by close();
   have old(len) <= 9223372036854775807u64 by close();
   have at(loop(2).entry, buf) == old(buf) + (old(len) - at(batch_entry, len)) by close() using {
    at(batch_entry, buf) == old(buf) + (old(len) - at(batch_entry, len));
   };
   have forall (k: int32) { 0 <= k and k < 5552 implies at(loop(2).entry, buf)[k] == (old(buf) + (old(len) - at(batch_entry, len)))[k] } by {
    intro() {
     intro() {
      have at(loop(2).entry, buf) + k == (old(buf) + (old(len) - at(batch_entry, len))) + k by {
       rewrite(at(loop(2).entry, buf), old(buf) + (old(len) - at(batch_entry, len)));
       close();
      }
      rewrite(at(loop(2).entry, buf) + k, (old(buf) + (old(len) - at(batch_entry, len))) + k);
      close();
     }
    }
   }
   apply(adler_sums_extensional(at(loop(2).entry, buf), old(buf) + (old(len) - at(batch_entry, len)), 5552, 5552, 5552));
   have to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(old(buf) + (old(len) - at(batch_entry, len)), 5552) by {
    rewrite(adler_byte_sum(old(buf) + (old(len) - at(batch_entry, len)), 5552), adler_byte_sum(at(loop(2).entry, buf), 5552));
    close() using { to_integer(adler) == to_integer(at(batch_entry, adler)) + adler_byte_sum(at(loop(2).entry, buf), 5552); };
   }
   have to_integer(sum2) == to_integer(at(batch_entry, sum2)) + 5552 * to_integer(at(batch_entry, adler)) + adler_weighted_sum(old(buf) + (old(len) - at(batch_entry, len)), 5552, 5552) by {
    rewrite(adler_weighted_sum(old(buf) + (old(len) - at(batch_entry, len)), 5552, 5552), adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552));
    close() using { to_integer(sum2) == to_integer(at(batch_entry, sum2)) + 5552 * to_integer(at(batch_entry, adler)) + adler_weighted_sum(at(loop(2).entry, buf), 5552, 5552); };
   }
   have 5552u64 <= at(batch_entry, len) by close();
   have to_integer(at(batch_entry, len)) <= to_integer(old(len));
   have to_integer(5552u64) <= to_integer(at(batch_entry, len));
   have to_integer(old(len) - at(batch_entry, len)) == to_integer(old(len)) - to_integer(at(batch_entry, len));
   have 0 <= to_integer(old(len)); have to_integer(old(len)) <= 18446744073709551615;
   have to_integer(old(len) - at(batch_entry, len)) + to_integer(5552u64) <= 18446744073709551615 by close() using {
    to_integer(old(len) - at(batch_entry, len)) == to_integer(old(len)) - to_integer(at(batch_entry, len));
    to_integer(5552u64) <= to_integer(at(batch_entry, len));
    to_integer(old(len)) <= 18446744073709551615;
   };
   have to_integer(5552) == to_integer(5552u64) by close();
   apply(zlib_general_seeded_batch_concat_u64(old(buf), old(len) - at(batch_entry, len), 5552, 5552u64, adler, sum2, at(batch_entry, adler), at(batch_entry, sum2), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
   apply(zlib_seeded_reduced_components(old(buf) + (old(len) - at(batch_entry, len)), 5552, adler, sum2, at(batch_entry, adler), at(batch_entry, sum2)));
   apply(zlib_full_stream_prefix_sum_u64(old(len), at(batch_entry, len), 5552u64));
   have to_integer(old(len) - len) == to_integer((old(len) - at(batch_entry, len)) + 5552u64) by close() using {
    to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
    to_integer(old(len) - (at(batch_entry, len) - 5552u64)) == to_integer((old(len) - at(batch_entry, len)) + 5552u64);
   };
   have viewable(buf[0u64..len]) by close() using {
    viewable(buf[0u64..16u64 * n as uint64 + len]); n == 0u32;
   };
   mark before_reductions;
   step();
   have separate(statement(7).statement(3).footprint, memory(buf[0u64..len])) by close();
   have viewable(buf[0u64..len]) by {
    preserve(memory(buf[0u64..len]), statement(7).statement(3));
   }
   step();
   have separate(statement(7).statement(4).footprint, memory(buf[0u64..len])) by close();
   have viewable(buf[0u64..len]) by {
    preserve(memory(buf[0u64..len]), statement(7).statement(4));
   }
   have adler == at(before_reductions, adler % 65521u64) by close();
   have sum2 == at(before_reductions, sum2 % 65521u64) by close();
   have to_integer(adler) == adler_spec_a_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler)))) by close() using {
    adler == at(before_reductions, adler % 65521u64);
    at(before_reductions, to_integer(adler % 65521u64)) == adler_spec_a_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler))));
   };
   have to_integer(sum2) == adler_spec_b_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using {
    sum2 == at(before_reductions, sum2 % 65521u64);
    at(before_reductions, to_integer(sum2 % 65521u64)) == adler_spec_b_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
   };
   have to_integer(adler) == adler_spec_a_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler)))) by close() using {
    to_integer(adler) == adler_spec_a_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler))));
    to_integer(old(len) - len) == to_integer((old(len) - at(batch_entry, len)) + 5552u64);
   };
   have to_integer(sum2) == adler_spec_b_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using {
    to_integer(sum2) == adler_spec_b_u64(old(buf), (old(len) - at(batch_entry, len)) + 5552u64, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
    to_integer(old(len) - len) == to_integer((old(len) - at(batch_entry, len)) + 5552u64);
   };
   have adler <= 65520u64 by close() using { adler == at(before_reductions, adler % 65521u64); at(before_reductions, adler % 65521u64 <= 65520u64); };
   have sum2 <= 65520u64 by close() using { sum2 == at(before_reductions, sum2 % 65521u64); at(before_reductions, sum2 % 65521u64 <= 65520u64); };
   have buf == at(batch_entry, buf) + 5552 by close() using { buf == at(loop(2).entry, buf) + zlib_batch_count(n); zlib_batch_count(n) == 5552; };
   apply(zlib_full_stream_remaining_step_u64(old(len), at(batch_entry, len), 5552u64));
   have len <= old(len) by close() using { to_integer(len) == to_integer(at(batch_entry, len) - 5552u64); to_integer(at(batch_entry, len) - 5552u64) <= to_integer(old(len)); };
   apply(zlib_full_prefix_advance_u64(old(buf), old(len), at(batch_entry, len), 5552u64));
   have buf == old(buf) + (old(len) - len) by close() using {
    buf == at(batch_entry, buf) + 5552;
    at(batch_entry, buf) == old(buf) + (old(len) - at(batch_entry, len));
    old(buf) + (old(len) - at(batch_entry, len)) + 5552u64 == old(buf) + (old(len) - (at(batch_entry, len) - 5552u64));
    to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
   };
   have len <= 9223372036854775807u64 by close() using { len <= old(len); old(len) <= 9223372036854775807u64; };

   have to_integer(len) == at(batch_entry, to_integer(len)) - 5552 by close() using {
    to_integer(len) == to_integer(at(batch_entry, len) - 5552u64);
    to_integer(at(batch_entry, len) - 5552u64) == at(batch_entry, to_integer(len)) - 5552;
   };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have to_integer(len) < at(batch_entry, to_integer(len)) by close() using { to_integer(len) == at(batch_entry, to_integer(len)) - 5552; };
  }

 }
 have len < 5552u64 by close();
 if len == 0u64 {
  have to_integer(old(len) - len) == to_integer(old(len)) by close() using { len == 0u64; };
  have to_integer(adler) == adler_spec_a_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler)))) by close() using { to_integer(adler) == adler_spec_a_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler)))); to_integer(old(len) - len) == to_integer(old(len)); };
  have to_integer(sum2) == adler_spec_b_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using { to_integer(sum2) == adler_spec_b_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))); to_integer(old(len) - len) == to_integer(old(len)); };
  have adler <= 65535u64 by close() using { adler <= 65520u64; };
  have sum2 <= 65535u64 by close() using { sum2 <= 65520u64; };
  apply(integer::uint64_pack_uint16_to_integer(adler, sum2));
  have to_integer(adler | (sum2 << 16)) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by {
   unfold(adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
   close() using { to_integer(adler | (sum2 << 16)) == to_integer(adler) + 65536 * to_integer(sum2); to_integer(adler) == adler_spec_a_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler)))); to_integer(sum2) == adler_spec_b_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))); };
  }
  step_until(function.exit); close();
 } else {
  have len <= 5551u64 by close() using { len < 5552u64; };
  have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
  // The remaining DO16 blocks start from the last batch's reduced seed.
  mark tail_entry;
  step(); step_until(loop(3).entry);
 loop {
  decreases to_integer(len);
  invariant 0 <= to_integer(zlib_seed_a(old(adler)));
  invariant to_integer(zlib_seed_a(old(adler))) <= 65520;
  invariant 0 <= to_integer(zlib_seed_b(old(adler)));
  invariant at(loop(3).entry, len) <= old(len);
  invariant at(loop(3).entry, buf) == old(buf) + (old(len) - at(loop(3).entry, len));
  invariant to_integer(at(loop(3).entry, adler)) == adler_spec_a_u64(old(buf), old(len) - at(loop(3).entry, len), to_integer(zlib_seed_a(old(adler))));
  invariant to_integer(at(loop(3).entry, sum2)) == adler_spec_b_u64(old(buf), old(len) - at(loop(3).entry, len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));

  invariant len <= at(loop(3).entry, len);
  invariant at(loop(3).entry, len) <= 5551u64;
  invariant at(loop(3).entry, adler) <= 65520u64;
  invariant at(loop(3).entry, sum2) <= 65520u64;
  invariant len <= old(len);
  invariant old(len) <= 9223372036854775807u64;
  invariant buf == old(buf) + (old(len) - len);
  invariant to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64);
  invariant to_integer(len) <= 5551;
  invariant buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - len);
  invariant viewable(buf[0u64..len]);
  invariant to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len));
  invariant to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len));
  initialize by {
   have len <= at(loop(3).entry, len) by close();
   have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
   have to_integer(at(loop(3).entry, len) - len) == to_integer(0u64) by close();
   have to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64) by {
    rewrite(to_integer(at(loop(3).entry, len) - len), to_integer(0u64));
    close();
   }
   have to_integer(len) <= to_integer(5551u64);
   have adler == at(loop(3).entry, adler) by close();
   have sum2 == at(loop(3).entry, sum2) by close();
   have to_integer(adler) <= to_integer(65520u64);
   have to_integer(sum2) <= to_integer(65520u64);
   have zlib_prefix_count(at(loop(3).entry, len), len) == 0 by { unfold(zlib_prefix_count(at(loop(3).entry, len), len)); close(); }
   apply(adler_sum_empty(at(loop(3).entry, buf), 0));
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), 0) by close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)); adler_byte_sum(at(loop(3).entry, buf), 0) == 0; };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(0) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), 0, 0) by close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)); adler_weighted_sum(at(loop(3).entry, buf), 0, 0) == 0; };
   have to_integer(adler) <= 65520 + 255 * to_integer(0) by close() using { to_integer(adler) <= 65520; };
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(0) by close() using { to_integer(sum2) <= 65520; };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len), 0); close(); }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len), 0); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len), 0); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(3).entry, len), len), 0); close(); }
   close();
  }
  maintain by {
   have 16u64 <= len by close();
   have len <= 5551u64 by close() using { len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
   have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
   have 1u64 <= len by close() using { 16u64 <= len; };
   have viewable(buf[0u64..16u64]) by close();
   apply(zlib_remaining_step(at(loop(3).entry, len), len, 16u64));
   have to_integer(at(loop(3).entry, len) - len) <= to_integer(2147483647u64) by { apply(integer::le_transitive(to_integer(at(loop(3).entry, len) - len), 5551, 2147483647)); }
   apply(zlib_full_prefix_observation(at(loop(3).entry, len), len));
   apply(zlib_prefix_observation(at(loop(3).entry, len), len));
   have to_integer(at(loop(3).entry, len) - len) < to_integer(at(loop(3).entry, len)) by close() using { 16u64 <= len; len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
   mark before_block;
   step();
   have to_integer(len) == to_integer(at(before_block, len - 16u64)) by close();
   have to_integer(len) == at(before_block, to_integer(len)) - 16 by close();
   step_until(assignment(adler, 22).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 0u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 0u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 0)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 0));
   have zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) == (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 0) as int32 by close();
   have buf[0] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))] by {
    rewrite(buf, at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)));
    rewrite(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 0) as int32);
    close();
   }
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)), adler, sum2, buf[0], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   have viewable(buf[0u64..1u64]) by close();
   mark byte_0;
   step();
   step_until(assignment(sum2, 22).entry);
   step();
   have separate(statement(8).statement(0).statement(1).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(1).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_0, adler + buf[0] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_0, adler + buf[0] as uint32 as uint64));
    at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1, zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_0, sum2 + (adler + buf[0] as uint32 as uint64)));
    at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1, zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by {
    rewrite(to_integer(adler), at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)));
    close() using { at(byte_0, to_integer(adler + buf[0] as uint32 as uint64)) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) by {
    rewrite(to_integer(sum2), at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))));
    close() using { at(byte_0, to_integer(sum2 + (adler + buf[0] as uint32 as uint64))) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1); };
   }
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by close();
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by close();
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by close();
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)) by close();
   step_until(assignment(adler, 23).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 1u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 1u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 1)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 1));
   have buf[1] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[1] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1), adler, sum2, buf[1], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_1;
   step();
   step_until(assignment(sum2, 23).entry);
   step();
   have separate(statement(8).statement(0).statement(3).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(3).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_1, adler + buf[1] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_1, adler + buf[1] as uint32 as uint64));
    at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_1, sum2 + (adler + buf[1] as uint32 as uint64)));
    at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by {
    rewrite(to_integer(adler), at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)));
    close() using { at(byte_1, to_integer(adler + buf[1] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by {
    rewrite(to_integer(sum2), at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))));
    close() using { at(byte_1, to_integer(sum2 + (adler + buf[1] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 1) + 1); };
   }
   step_until(assignment(adler, 24).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 2u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 2u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 2)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 2));
   have buf[2] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[2] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2), adler, sum2, buf[2], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_2;
   step();
   step_until(assignment(sum2, 24).entry);
   step();
   have separate(statement(8).statement(0).statement(6).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(6).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_2, adler + buf[2] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_2, adler + buf[2] as uint32 as uint64));
    at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_2, sum2 + (adler + buf[2] as uint32 as uint64)));
    at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by {
    rewrite(to_integer(adler), at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)));
    close() using { at(byte_2, to_integer(adler + buf[2] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by {
    rewrite(to_integer(sum2), at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))));
    close() using { at(byte_2, to_integer(sum2 + (adler + buf[2] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 2) + 1); };
   }
   step_until(assignment(adler, 25).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 3u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 3u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 3)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 3));
   have buf[3] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[3] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3), adler, sum2, buf[3], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_3;
   step();
   step_until(assignment(sum2, 25).entry);
   step();
   have separate(statement(8).statement(0).statement(8).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(8).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_3, adler + buf[3] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_3, adler + buf[3] as uint32 as uint64));
    at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_3, sum2 + (adler + buf[3] as uint32 as uint64)));
    at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by {
    rewrite(to_integer(adler), at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)));
    close() using { at(byte_3, to_integer(adler + buf[3] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by {
    rewrite(to_integer(sum2), at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))));
    close() using { at(byte_3, to_integer(sum2 + (adler + buf[3] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 3) + 1); };
   }
   step_until(assignment(adler, 26).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 4u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 4u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 4)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 4));
   have buf[4] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[4] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4), adler, sum2, buf[4], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_4;
   step();
   step_until(assignment(sum2, 26).entry);
   step();
   have separate(statement(8).statement(0).statement(12).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(12).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_4, adler + buf[4] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_4, adler + buf[4] as uint32 as uint64));
    at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_4, sum2 + (adler + buf[4] as uint32 as uint64)));
    at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by {
    rewrite(to_integer(adler), at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)));
    close() using { at(byte_4, to_integer(adler + buf[4] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by {
    rewrite(to_integer(sum2), at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))));
    close() using { at(byte_4, to_integer(sum2 + (adler + buf[4] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 4) + 1); };
   }
   step_until(assignment(adler, 27).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 5u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 5u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 5)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 5));
   have buf[5] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[5] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5), adler, sum2, buf[5], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_5;
   step();
   step_until(assignment(sum2, 27).entry);
   step();
   have separate(statement(8).statement(0).statement(14).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(14).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_5, adler + buf[5] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_5, adler + buf[5] as uint32 as uint64));
    at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_5, sum2 + (adler + buf[5] as uint32 as uint64)));
    at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by {
    rewrite(to_integer(adler), at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)));
    close() using { at(byte_5, to_integer(adler + buf[5] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by {
    rewrite(to_integer(sum2), at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))));
    close() using { at(byte_5, to_integer(sum2 + (adler + buf[5] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 5) + 1); };
   }
   step_until(assignment(adler, 28).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 6u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 6u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 6)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 6));
   have buf[6] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[6] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6), adler, sum2, buf[6], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_6;
   step();
   step_until(assignment(sum2, 28).entry);
   step();
   have separate(statement(8).statement(0).statement(17).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(17).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_6, adler + buf[6] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_6, adler + buf[6] as uint32 as uint64));
    at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_6, sum2 + (adler + buf[6] as uint32 as uint64)));
    at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by {
    rewrite(to_integer(adler), at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)));
    close() using { at(byte_6, to_integer(adler + buf[6] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by {
    rewrite(to_integer(sum2), at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))));
    close() using { at(byte_6, to_integer(sum2 + (adler + buf[6] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 6) + 1); };
   }
   step_until(assignment(adler, 29).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 7u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 7u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 7)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 7));
   have buf[7] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[7] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7), adler, sum2, buf[7], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_7;
   step();
   step_until(assignment(sum2, 29).entry);
   step();
   have separate(statement(8).statement(0).statement(19).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(19).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_7, adler + buf[7] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_7, adler + buf[7] as uint32 as uint64));
    at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_7, sum2 + (adler + buf[7] as uint32 as uint64)));
    at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by {
    rewrite(to_integer(adler), at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)));
    close() using { at(byte_7, to_integer(adler + buf[7] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by {
    rewrite(to_integer(sum2), at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))));
    close() using { at(byte_7, to_integer(sum2 + (adler + buf[7] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 7) + 1); };
   }
   step_until(assignment(adler, 30).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 8u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 8u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 8)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 8));
   have buf[8] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[8] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8), adler, sum2, buf[8], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_8;
   step();
   step_until(assignment(sum2, 30).entry);
   step();
   have separate(statement(8).statement(0).statement(24).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(24).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_8, adler + buf[8] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_8, adler + buf[8] as uint32 as uint64));
    at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_8, sum2 + (adler + buf[8] as uint32 as uint64)));
    at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by {
    rewrite(to_integer(adler), at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)));
    close() using { at(byte_8, to_integer(adler + buf[8] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by {
    rewrite(to_integer(sum2), at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))));
    close() using { at(byte_8, to_integer(sum2 + (adler + buf[8] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 8) + 1); };
   }
   step_until(assignment(adler, 31).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 9u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 9u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 9)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 9));
   have buf[9] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[9] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9), adler, sum2, buf[9], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_9;
   step();
   step_until(assignment(sum2, 31).entry);
   step();
   have separate(statement(8).statement(0).statement(26).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(26).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_9, adler + buf[9] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_9, adler + buf[9] as uint32 as uint64));
    at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_9, sum2 + (adler + buf[9] as uint32 as uint64)));
    at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by {
    rewrite(to_integer(adler), at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)));
    close() using { at(byte_9, to_integer(adler + buf[9] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by {
    rewrite(to_integer(sum2), at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))));
    close() using { at(byte_9, to_integer(sum2 + (adler + buf[9] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 9) + 1); };
   }
   step_until(assignment(adler, 32).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 10u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 10u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 10)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 10));
   have buf[10] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[10] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10), adler, sum2, buf[10], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_10;
   step();
   step_until(assignment(sum2, 32).entry);
   step();
   have separate(statement(8).statement(0).statement(29).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(29).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_10, adler + buf[10] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_10, adler + buf[10] as uint32 as uint64));
    at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_10, sum2 + (adler + buf[10] as uint32 as uint64)));
    at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by {
    rewrite(to_integer(adler), at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)));
    close() using { at(byte_10, to_integer(adler + buf[10] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by {
    rewrite(to_integer(sum2), at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))));
    close() using { at(byte_10, to_integer(sum2 + (adler + buf[10] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 10) + 1); };
   }
   step_until(assignment(adler, 33).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 11u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 11u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 11)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 11));
   have buf[11] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[11] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11), adler, sum2, buf[11], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_11;
   step();
   step_until(assignment(sum2, 33).entry);
   step();
   have separate(statement(8).statement(0).statement(31).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(31).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_11, adler + buf[11] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_11, adler + buf[11] as uint32 as uint64));
    at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_11, sum2 + (adler + buf[11] as uint32 as uint64)));
    at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by {
    rewrite(to_integer(adler), at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)));
    close() using { at(byte_11, to_integer(adler + buf[11] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by {
    rewrite(to_integer(sum2), at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))));
    close() using { at(byte_11, to_integer(sum2 + (adler + buf[11] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 11) + 1); };
   }
   step_until(assignment(adler, 34).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 12u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 12u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 12)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 12));
   have buf[12] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[12] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12), adler, sum2, buf[12], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_12;
   step();
   step_until(assignment(sum2, 34).entry);
   step();
   have separate(statement(8).statement(0).statement(35).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(35).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_12, adler + buf[12] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_12, adler + buf[12] as uint32 as uint64));
    at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_12, sum2 + (adler + buf[12] as uint32 as uint64)));
    at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by {
    rewrite(to_integer(adler), at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)));
    close() using { at(byte_12, to_integer(adler + buf[12] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by {
    rewrite(to_integer(sum2), at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))));
    close() using { at(byte_12, to_integer(sum2 + (adler + buf[12] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 12) + 1); };
   }
   step_until(assignment(adler, 35).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 13u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 13u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 13)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 13));
   have buf[13] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[13] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13), adler, sum2, buf[13], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_13;
   step();
   step_until(assignment(sum2, 35).entry);
   step();
   have separate(statement(8).statement(0).statement(37).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(37).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_13, adler + buf[13] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_13, adler + buf[13] as uint32 as uint64));
    at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_13, sum2 + (adler + buf[13] as uint32 as uint64)));
    at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by {
    rewrite(to_integer(adler), at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)));
    close() using { at(byte_13, to_integer(adler + buf[13] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by {
    rewrite(to_integer(sum2), at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))));
    close() using { at(byte_13, to_integer(sum2 + (adler + buf[13] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 13) + 1); };
   }
   step_until(assignment(adler, 36).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 14u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 14u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 14)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 14));
   have buf[14] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[14] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14), adler, sum2, buf[14], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_14;
   step();
   step_until(assignment(sum2, 36).entry);
   step();
   have separate(statement(8).statement(0).statement(40).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(40).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_14, adler + buf[14] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_14, adler + buf[14] as uint32 as uint64));
    at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_14, sum2 + (adler + buf[14] as uint32 as uint64)));
    at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by {
    rewrite(to_integer(adler), at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)));
    close() using { at(byte_14, to_integer(adler + buf[14] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by {
    rewrite(to_integer(sum2), at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))));
    close() using { at(byte_14, to_integer(sum2 + (adler + buf[14] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 14) + 1); };
   }
   step_until(assignment(adler, 37).entry);
   apply(zlib_block_read_bound(at(loop(3).entry, len), at(before_block, len), 15u64));
   apply(zlib_full_stream_tail_read_bound_u64(old(len), at(before_block, len), 15u64));
   apply(zlib_block_lane_defined(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 15)); apply(zlib_block_lane(at(loop(3).entry, buf), at(loop(3).entry, len), at(before_block, len), 15));
   have buf[15] == at(loop(3).entry, buf)[(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15)] by close() using {
    buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len));
    (at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)))[15] == at(loop(3).entry, buf)[zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15];
   };
   apply(zlib_seeded_component_step(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15), adler, sum2, buf[15], at(loop(3).entry, adler), at(loop(3).entry, sum2)));
   mark byte_15;
   step();
   step_until(assignment(sum2, 37).entry);
   step();
   have separate(statement(8).statement(0).statement(42).statement(1).footprint, at(before_block, memory(buf[0u64..len]))) by close();
   have viewable(at(before_block, memory(buf[0u64..len]))) by {
    preserve(at(before_block, memory(buf[0u64..len])), statement(8).statement(0).statement(42).statement(1));
   }
   have to_integer(adler) == to_integer(at(byte_15, adler + buf[15] as uint32 as uint64)) by close();
   have to_integer(sum2) == to_integer(at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64))) by close();
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by close() using {
    to_integer(adler) == to_integer(at(byte_15, adler + buf[15] as uint32 as uint64));
    at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by close() using {
    to_integer(sum2) == to_integer(at(byte_15, sum2 + (adler + buf[15] as uint32 as uint64)));
    at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1);
   };
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by {
    rewrite(to_integer(adler), at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)));
    close() using { at(byte_15, to_integer(adler + buf[15] as uint32 as uint64)) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by {
    rewrite(to_integer(sum2), at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))));
    close() using { at(byte_15, to_integer(sum2 + (adler + buf[15] as uint32 as uint64))) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   have (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) == ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) by close() using {
    0 <= zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)); zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) <= 22208;
   };
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1, (zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(adler) <= 65520 + 255 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)) by {
    rewrite((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), ((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1));
    close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer((zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 15) + 1); };
   }
   step_until(loop.back_edge);
   have len <= at(loop(3).entry, len) by close();
   have to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64) by {
    apply(integer::uint64_subtract_to_integer(at(loop(3).entry, len), len));
    have 0 <= to_integer(len) by close();
    have to_integer(at(loop(3).entry, len)) <= 5551 by close() using { at(loop(3).entry, len) <= 5551u64; };
    rewrite(to_integer(at(loop(3).entry, len) - len), to_integer(at(loop(3).entry, len)) - to_integer(len));
    apply(integer::subtract_le(to_integer(at(loop(3).entry, len)), 5551, to_integer(len), 0));
    close();
   }
   have to_integer(len) <= 5551 by close() using { to_integer(len) == at(before_block, to_integer(len)) - 16; at(before_block, to_integer(len)) <= 5551; };
   have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
   have len <= 5551u64;
   have len <= 9223372036854775807u64 by close() using { len <= 5551u64; };
   have to_integer(len) < at(before_block, to_integer(len)) by close() using { to_integer(len) == at(before_block, to_integer(len)) - 16; };
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + 16 by close();
   have -2147483648 <= to_integer(zlib_prefix_count(at(loop(3).entry, len), len)); have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= 2147483647;
   have -2147483648 <= to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))); have to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) <= 2147483647;
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + to_integer(16) >= -2147483648 by close() using { -2147483648 <= to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))); };
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + to_integer(16) <= 2147483647 by {
    apply(integer::int32_less_equal_to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)), 22208));
    apply(integer::add_le(to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))), 22208, 16, 16));
    apply(integer::le_transitive(to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + 16, 22208 + 16, 2147483647));
   }
   have defined(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16);
   have defined(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) by close();
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + to_integer(16);
   have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16) by {
    rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16), to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + to_integer(16));
    close() using { to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len))) + 16; };
   }
   have buf == at(before_block, buf) + 16 by close();
   have to_integer(at(loop(3).entry, len) - len) == to_integer((at(loop(3).entry, len) - at(before_block, len)) + 16u64) by close() using {
    to_integer(len) == to_integer(at(before_block, len - 16u64));
    16u64 <= at(before_block, len);
    at(before_block, len) <= at(loop(3).entry, len);
    at(loop(3).entry, len) <= 5551u64;
   };
   have to_integer(at(loop(3).entry, len) - at(before_block, len)) + 16 <= 18446744073709551615 by {
    apply(integer::add_le(to_integer(at(loop(3).entry, len) - at(before_block, len)), 5535, 16, 16));
    apply(integer::le_transitive(to_integer(at(loop(3).entry, len) - at(before_block, len)) + 16, 5535 + 16, 18446744073709551615));
   }
   apply(integer::uint8_pointer_add_associate_uint64(at(loop(3).entry, buf), at(loop(3).entry, len) - at(before_block, len), 16u64));
   have (at(loop(3).entry, len) - len) as uint64 == ((at(loop(3).entry, len) - at(before_block, len)) + 16u64) as uint64 by close() using {
    to_integer(at(loop(3).entry, len) - len) == to_integer((at(loop(3).entry, len) - at(before_block, len)) + 16u64);
   };
   have buf == at(loop(3).entry, buf) + (at(loop(3).entry, len) - len) by {
    rewrite(buf, at(before_block, buf) + 16);
    rewrite(at(before_block, buf), at(loop(3).entry, buf) + (at(loop(3).entry, len) - at(before_block, len)));
    rewrite((at(loop(3).entry, len) - len) as uint64, ((at(loop(3).entry, len) - at(before_block, len)) + 16u64) as uint64);
    close();
   }
   have len == at(before_block, len - 16u64) by close();
   apply(click::separation::contains_subrange(at(before_block, buf), 0u64, at(before_block, len), 16u64, at(before_block, len)));
   have contains(memory(at(before_block, buf)[16u64..at(before_block, len)]), memory(buf[0u64..len])) by {
    rewrite(buf, at(before_block, buf) + 16);
    rewrite(len, at(before_block, len - 16u64));
    apply(click::separation::contains_rebase(at(before_block, buf), 16u64, at(before_block, len)));
   }
   apply(click::separation::contains_trans(at(before_block, memory(buf[0u64..len])), memory(at(before_block, buf)[16u64..at(before_block, len)]), memory(buf[0u64..len])));
   apply(click::separation::viewable_restrict(at(before_block, memory(buf[0u64..len])), memory(buf[0u64..len])));
   have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), len)), to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)); close(); }
   have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), len)), to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)); close(); }
   have to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), len)), to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)); close(); }
   have to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) by { rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), len)), to_integer(zlib_prefix_count(at(loop(3).entry, len), at(before_block, len)) + 16)); close(); }
   have len <= old(len) by {
    have to_integer(len) <= to_integer(at(before_block, len)) by close() using {
     to_integer(len) == at(before_block, to_integer(len)) - 16;
    };
    apply(integer::uint64_to_integer_less_equal_implies_less_equal(len, at(before_block, len)));
    apply(integer::uint64_less_equal_transitive(len, at(before_block, len), old(len)));
   }
   apply(zlib_full_prefix_advance_u64(old(buf), old(len), at(before_block, len), 16u64));
   have to_integer(len) == to_integer(at(before_block, len) - 16u64) by close();
   have buf == old(buf) + (old(len) - len) by close() using {
    buf == at(before_block, buf) + 16;
    at(before_block, buf) == old(buf) + (old(len) - at(before_block, len));
    old(buf) + (old(len) - at(before_block, len)) + 16u64 == old(buf) + (old(len) - (at(before_block, len) - 16u64));
    to_integer(len) == to_integer(at(before_block, len) - 16u64);
   };
  }
 }
 have len <= 15u64 by close() using { not (len >= 16u64); len <= at(loop(3).entry, len); at(loop(3).entry, len) <= 5551u64; };
 have to_integer(len) <= to_integer(15u64);
  // The original C performs no MOD between the DO16 and scalar tail loops.
  step_until(loop(4).entry);
  have to_integer(at(loop(3).entry, len) - len) <= to_integer(2147483647u64) by {
   apply(integer::uint64_subtract_to_integer(at(loop(3).entry, len), len));
   have to_integer(at(loop(3).entry, len)) <= 2147483647 by {
    apply(integer::le_transitive(to_integer(at(loop(3).entry, len)), 5551, 2147483647));
   }
   have 0 <= to_integer(len) by close();
   rewrite(to_integer(at(loop(3).entry, len) - len), to_integer(at(loop(3).entry, len)) - to_integer(len));
   apply(integer::subtract_le(to_integer(at(loop(3).entry, len)), 2147483647, to_integer(len), 0));
   close();
  }
  apply(zlib_full_prefix_observation(at(loop(3).entry, len), len));
  have at(loop(3).entry, buf) == (old(buf) + (old(len) - at(loop(3).entry, len))) by close();
  have forall (k: int32) { 0 <= k and k < zlib_prefix_count(at(loop(3).entry, len), len) implies at(loop(3).entry, buf)[k] == (old(buf) + (old(len) - at(loop(3).entry, len)))[k] } by {
   intro() {
    intro() {
     have at(loop(3).entry, buf) + k == (old(buf) + (old(len) - at(loop(3).entry, len))) + k by {
      rewrite(at(loop(3).entry, buf), (old(buf) + (old(len) - at(loop(3).entry, len))));
      close();
     }
     rewrite(at(loop(3).entry, buf) + k, (old(buf) + (old(len) - at(loop(3).entry, len))) + k);
     close();
    }
   }
  }
  apply(adler_sums_extensional(at(loop(3).entry, buf), (old(buf) + (old(len) - at(loop(3).entry, len))), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)));
  have to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum((old(buf) + (old(len) - at(loop(3).entry, len))), zlib_prefix_count(at(loop(3).entry, len), len)) by {
   rewrite(adler_byte_sum((old(buf) + (old(len) - at(loop(3).entry, len))), zlib_prefix_count(at(loop(3).entry, len), len)), adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)));
   close() using { to_integer(adler) == to_integer(at(loop(3).entry, adler)) + adler_byte_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len)); };
  }
  have to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum((old(buf) + (old(len) - at(loop(3).entry, len))), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)) by {
   rewrite(adler_weighted_sum((old(buf) + (old(len) - at(loop(3).entry, len))), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)), adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)));
   close() using { to_integer(sum2) == to_integer(at(loop(3).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) * to_integer(at(loop(3).entry, adler)) + adler_weighted_sum(at(loop(3).entry, buf), zlib_prefix_count(at(loop(3).entry, len), len), zlib_prefix_count(at(loop(3).entry, len), len)); };
  }
  have to_integer(len) <= to_integer(at(loop(3).entry, len));
  have to_integer(at(loop(3).entry, len)) <= to_integer(old(len));
  have to_integer(old(len) - at(loop(3).entry, len)) == to_integer(old(len)) - to_integer(at(loop(3).entry, len));
  have to_integer(at(loop(3).entry, len) - len) == to_integer(at(loop(3).entry, len)) - to_integer(len);
  have 0 <= to_integer(old(len)); have to_integer(old(len)) <= 18446744073709551615; have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
  have to_integer(old(len) - at(loop(3).entry, len)) + to_integer(at(loop(3).entry, len) - len) <= 18446744073709551615 by close() using {
   to_integer(old(len) - at(loop(3).entry, len)) == to_integer(old(len)) - to_integer(at(loop(3).entry, len));
   to_integer(at(loop(3).entry, len) - len) == to_integer(at(loop(3).entry, len)) - to_integer(len);
   to_integer(old(len)) <= 18446744073709551615; 0 <= to_integer(len);
  };
  apply(zlib_general_seeded_batch_concat_u64(old(buf), old(len) - at(loop(3).entry, len), zlib_prefix_count(at(loop(3).entry, len), len), at(loop(3).entry, len) - len, adler, sum2, at(loop(3).entry, adler), at(loop(3).entry, sum2), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
  have to_integer((old(len) - at(loop(3).entry, len)) + (at(loop(3).entry, len) - len)) == to_integer(old(len) - len) by close() using { len <= at(loop(3).entry, len); at(loop(3).entry, len) <= old(len); };
  have to_integer(adler % 65521u64) == adler_spec_a_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler)))) by close() using {
   to_integer(adler % 65521u64) == adler_spec_a_u64(old(buf), (old(len) - at(loop(3).entry, len)) + (at(loop(3).entry, len) - len), to_integer(zlib_seed_a(old(adler))));
   to_integer((old(len) - at(loop(3).entry, len)) + (at(loop(3).entry, len) - len)) == to_integer(old(len) - len);
  };
  have to_integer(sum2 % 65521u64) == adler_spec_b_u64(old(buf), old(len) - len, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using {
   to_integer(sum2 % 65521u64) == adler_spec_b_u64(old(buf), (old(len) - at(loop(3).entry, len)) + (at(loop(3).entry, len) - len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
   to_integer((old(len) - at(loop(3).entry, len)) + (at(loop(3).entry, len) - len)) == to_integer(old(len) - len);
  };
  have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= to_integer(2147483647);
  have to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64);
  have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= to_integer(5551) by {
   rewrite(to_integer(zlib_prefix_count(at(loop(3).entry, len), len)), to_integer(at(loop(3).entry, len) - len));
   close() using { to_integer(at(loop(3).entry, len) - len) <= to_integer(5551u64); };
  }
  have zlib_prefix_count(at(loop(3).entry, len), len) <= 5551;
  have to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= to_integer(5551);
  have to_integer(adler) <= 1500000 by close() using { to_integer(adler) <= 65520 + 255 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)); to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= 5551; };
  have to_integer(sum2) <= 10000000000 by close() using { to_integer(sum2) <= 65520 + 1481280 * to_integer(zlib_prefix_count(at(loop(3).entry, len), len)); to_integer(zlib_prefix_count(at(loop(3).entry, len), len)) <= 5551; };
  have adler <= 1500000u64;
  have sum2 <= 10000000000u64;
  loop {
   decreases to_integer(len);
  invariant 0 <= to_integer(zlib_seed_a(old(adler)));
  invariant to_integer(zlib_seed_a(old(adler))) <= 65520;
  invariant 0 <= to_integer(zlib_seed_b(old(adler)));
   invariant len <= at(loop(4).entry, len);
   invariant at(loop(4).entry, len) <= 15u64;
   invariant at(loop(4).entry, len) <= old(len);
   invariant old(len) <= 9223372036854775807u64;
   invariant len <= old(len);
   invariant buf == at(loop(4).entry, buf) + (at(loop(4).entry, len) - len);
   invariant buf == old(buf) + (old(len) - len);
   invariant at(loop(4).entry, buf) == old(buf) + (old(len) - at(loop(4).entry, len));
   invariant forall (k: uint64) { k < len implies load<uint8>(buf + k) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k] };
   invariant viewable(buf[0u64..len]);
   invariant at(loop(4).entry, adler) <= 1500000u64;
   invariant at(loop(4).entry, sum2) <= 10000000000u64;
   invariant to_integer(at(loop(4).entry, adler) % 65521u64) == adler_spec_a_u64(old(buf), old(len) - at(loop(4).entry, len), to_integer(zlib_seed_a(old(adler))));
   invariant to_integer(at(loop(4).entry, sum2) % 65521u64) == adler_spec_b_u64(old(buf), old(len) - at(loop(4).entry, len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
   invariant to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len));
   invariant to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len));
   initialize by {
    have len <= 9223372036854775807u64 by close() using { len <= 15u64; };
    have zlib_prefix_count(at(loop(4).entry, len), len) == 0 by { unfold(zlib_prefix_count(at(loop(4).entry, len), len)); close(); }
    have (at(loop(4).entry, len) - len) as uint64 == 0u64 by close();
    have forall (k: uint64) { k < len implies load<uint8>(buf + k) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k] } by {
     intro() {
      intro() {
       close();
      }
     }
    }
    apply(adler_sum_empty(at(loop(4).entry, buf), 0));
    have to_integer(adler) <= to_integer(1500000u64);
    have to_integer(sum2) <= to_integer(10000000000u64);
    have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len), 0); close() using { adler_byte_sum(at(loop(4).entry, buf), 0) == 0; }; }
    have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len), 0); close() using { adler_weighted_sum(at(loop(4).entry, buf), 0, 0) == 0; }; }
    have to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len), 0); close() using { to_integer(adler) <= 1500000; }; }
    have to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by { rewrite(zlib_prefix_count(at(loop(4).entry, len), len), 0); close() using { to_integer(sum2) <= 10000000000; }; }
    close();
   }
   maintain by {
    if len == 0u64 {
     // Record the checksum before the zero guard decrements len to UINT64_MAX.
     have to_integer(at(loop(4).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), len));
      have to_integer(at(loop(4).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(4).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(4).entry, len) - len), to_integer(at(loop(4).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_observation(at(loop(4).entry, len), len));
     have at(loop(4).entry, buf) == (old(buf) + (old(len) - at(loop(4).entry, len))) by close();
     have forall (k: int32) { 0 <= k and k < zlib_prefix_count(at(loop(4).entry, len), len) implies at(loop(4).entry, buf)[k] == (old(buf) + (old(len) - at(loop(4).entry, len)))[k] } by {
      intro() {
       intro() {
        have at(loop(4).entry, buf) + k == (old(buf) + (old(len) - at(loop(4).entry, len))) + k by {
         rewrite(at(loop(4).entry, buf), (old(buf) + (old(len) - at(loop(4).entry, len))));
         close();
        }
        rewrite(at(loop(4).entry, buf) + k, (old(buf) + (old(len) - at(loop(4).entry, len))) + k);
        close();
       }
      }
     }
     apply(adler_sums_extensional(at(loop(4).entry, buf), (old(buf) + (old(len) - at(loop(4).entry, len))), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)));
     have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum((old(buf) + (old(len) - at(loop(4).entry, len))), zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(adler_byte_sum((old(buf) + (old(len) - at(loop(4).entry, len))), zlib_prefix_count(at(loop(4).entry, len), len)), adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)));
      close() using { to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)); };
     }
     have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum((old(buf) + (old(len) - at(loop(4).entry, len))), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(adler_weighted_sum((old(buf) + (old(len) - at(loop(4).entry, len))), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)), adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)));
      close() using { to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)); };
     }
     have to_integer(len) <= to_integer(at(loop(4).entry, len));
     have to_integer(at(loop(4).entry, len)) <= to_integer(old(len));
     have to_integer(old(len) - at(loop(4).entry, len)) == to_integer(old(len)) - to_integer(at(loop(4).entry, len));
     have to_integer(at(loop(4).entry, len) - len) == to_integer(at(loop(4).entry, len)) - to_integer(len);
     have 0 <= to_integer(old(len)); have to_integer(old(len)) <= 18446744073709551615; have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
     have to_integer(old(len) - at(loop(4).entry, len)) + to_integer(at(loop(4).entry, len) - len) <= 18446744073709551615 by close() using {
      to_integer(old(len) - at(loop(4).entry, len)) == to_integer(old(len)) - to_integer(at(loop(4).entry, len));
      to_integer(at(loop(4).entry, len) - len) == to_integer(at(loop(4).entry, len)) - to_integer(len);
      to_integer(old(len)) <= 18446744073709551615; 0 <= to_integer(len);
     };
     apply(zlib_general_raw_seeded_batch_concat_u64(old(buf), old(len) - at(loop(4).entry, len), zlib_prefix_count(at(loop(4).entry, len), len), at(loop(4).entry, len) - len, adler, sum2, at(loop(4).entry, adler), at(loop(4).entry, sum2), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
     have to_integer((old(len) - at(loop(4).entry, len)) + (at(loop(4).entry, len) - len)) == to_integer(old(len)) by close() using { len == 0u64; len <= at(loop(4).entry, len); at(loop(4).entry, len) <= old(len); };
     have to_integer(adler % 65521u64) == adler_spec_a_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler)))) by close() using {
      to_integer(adler % 65521u64) == adler_spec_a_u64(old(buf), (old(len) - at(loop(4).entry, len)) + (at(loop(4).entry, len) - len), to_integer(zlib_seed_a(old(adler))));
      to_integer((old(len) - at(loop(4).entry, len)) + (at(loop(4).entry, len) - len)) == to_integer(old(len));
     };
     have to_integer(sum2 % 65521u64) == adler_spec_b_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) by close() using {
      to_integer(sum2 % 65521u64) == adler_spec_b_u64(old(buf), (old(len) - at(loop(4).entry, len)) + (at(loop(4).entry, len) - len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));
      to_integer((old(len) - at(loop(4).entry, len)) + (at(loop(4).entry, len) - len)) == to_integer(old(len));
     };
     apply(zlib_general_components_pack_u64(old(buf), old(len), adler, sum2, to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))));
     step(); step();
    } else {
     have 0u64 <= len by close();
     have 0u64 < len by {
      if 0u64 < len { close(); } else {
       have 0u64 == len;
       have len == 0u64 by { rewrite(0u64, len); close(); }
       contradiction(len == 0u64);
      }
     }
     have to_integer(0u64) < to_integer(len);
     have to_integer(1u64) <= to_integer(len) by close() using { to_integer(0u64) < to_integer(len); };
     have 1u64 <= len;
     have len <= 15u64 by close() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     have to_integer(len - 1u64) == to_integer(len) - to_integer(1u64);
     have at(loop(4).entry, len) <= 2147483647u64 by {
      apply(integer::uint64_less_equal_transitive(at(loop(4).entry, len), 15u64, 2147483647u64));
     }
     apply(zlib_full_stream_remaining_step(at(loop(4).entry, len), len, 1u64));
     apply(zlib_full_stream_prefix_step(at(loop(4).entry, len), len, 1u64));
     have to_integer(at(loop(4).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), len));
      have to_integer(at(loop(4).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(4).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(4).entry, len) - len), to_integer(at(loop(4).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_observation(at(loop(4).entry, len), len));
     have to_integer(at(loop(4).entry, len) - len) <= to_integer(15u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), len));
      have to_integer(at(loop(4).entry, len)) <= 15 by close() using { at(loop(4).entry, len) <= 15u64; };
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(4).entry, len) - len), to_integer(at(loop(4).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 15, to_integer(len), 0));
      close();
     }
     have to_integer(at(loop(4).entry, len) - len) <= to_integer(15u64);
     have to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) <= to_integer(15) by {
      rewrite(to_integer(zlib_prefix_count(at(loop(4).entry, len), len)), to_integer(at(loop(4).entry, len) - len));
      close() using { to_integer(at(loop(4).entry, len) - len) <= to_integer(15u64); };
     }
     have zlib_prefix_count(at(loop(4).entry, len), len) <= 15;
     have 15 < 16 by close();
     have zlib_prefix_count(at(loop(4).entry, len), len) < 16;
     have viewable(buf[0u64..1u64]) by close();
     mark before_decrement;
     have forall (k: uint64) { k < at(before_decrement, len) implies at(before_decrement, load<uint8>(buf + k)) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k] } by {
      intro() {
       intro() {
        have k < len by close();
        instantiate(forall (k: uint64) { k < len implies load<uint8>(buf + k) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k] }, k);
        close() using { load<uint8>(buf + k) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k]; };
       }
      }
     }
     step(); step();
     have to_integer(len) == to_integer(at(before_decrement, len) - 1u64) by close();
     have to_integer(len) == at(before_decrement, to_integer(len)) - 1 by close();
     step_until(assignment(adler, 38).entry);
     apply(zlib_full_stream_scalar_read_bound_u64(old(len), at(before_decrement, len)));
     have to_integer(at(loop(4).entry, len) - at(before_decrement, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), at(before_decrement, len)));
      have to_integer(at(loop(4).entry, len)) <= 2147483647 by {
       apply(integer::le_transitive(to_integer(at(loop(4).entry, len)), 15, 2147483647));
      }
      have 0 <= to_integer(at(before_decrement, len)) by close();
      rewrite(to_integer(at(loop(4).entry, len) - at(before_decrement, len)), to_integer(at(loop(4).entry, len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 2147483647, to_integer(at(before_decrement, len)), 0));
      close();
     }
     apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), at(before_decrement, len)));
     have at(before_decrement, buf) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) by {
      rewrite(at(before_decrement, buf), at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)));
      close() using { at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)); };
     }
     have 0u64 < at(before_decrement, len) by close();
     instantiate(forall (k: uint64) { k < at(before_decrement, len) implies at(before_decrement, load<uint8>(buf + k)) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k] }, 0u64);
     have at(before_decrement, buf[0]) == at(before_decrement, load<uint8>(buf + 0u64)) by close();
     have (at(loop(4).entry, len) - at(before_decrement, len)) as uint64 == ((at(loop(4).entry, len) - at(before_decrement, len)) + 0u64) as uint64 by close();
     have at(loop(4).entry, buf)[at(loop(4).entry, len) - at(before_decrement, len)] == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + 0u64] by {
      rewrite((at(loop(4).entry, len) - at(before_decrement, len)) as uint64, ((at(loop(4).entry, len) - at(before_decrement, len)) + 0u64) as uint64);
      close();
     }
     have at(loop(4).entry, buf)[at(loop(4).entry, len) - at(before_decrement, len)] == at(loop(4).entry, buf)[zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len))] by close() using {
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len));
     };
     have at(before_decrement, buf[0]) == at(loop(4).entry, buf)[zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len))] by {
      rewrite(at(loop(4).entry, buf)[zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len))], at(loop(4).entry, buf)[at(loop(4).entry, len) - at(before_decrement, len)]);
      rewrite(at(loop(4).entry, buf)[at(loop(4).entry, len) - at(before_decrement, len)], at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + 0u64]);
      close() using { at(before_decrement, load<uint8>(buf + 0u64)) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + 0u64]; };
     }
     apply(zlib_scalar_seeded_component_step(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)), adler, sum2, at(before_decrement, buf[0]), at(loop(4).entry, adler), at(loop(4).entry, sum2)));
     mark before_add;
     step(); step_until(assignment(sum2, 38).entry); step();
     have separate(statement(8).statement(1).statement(1).footprint, at(before_decrement, memory(buf[0u64..len]))) by close();
     have viewable(at(before_decrement, memory(buf[0u64..len]))) by {
      preserve(at(before_decrement, memory(buf[0u64..len])), statement(8).statement(1).statement(1));
     }
     have forall (k: uint64) { k < at(before_decrement, len) implies at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k] } by {
      intro() {
       intro() {
        have separate(statement(8).statement(1).statement(1).footprint, at(before_decrement, memory((buf + k)[0..1]))) by close();
        have at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) by {
         preserve(at(before_decrement, memory((buf + k)[0..1])), statement(8).statement(1).statement(1));
        }
        have at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) == at(before_decrement, load<uint8>(buf + k)) by close();
        instantiate(forall (k: uint64) { k < at(before_decrement, len) implies at(before_decrement, load<uint8>(buf + k)) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k] }, k);
        close() using {
         at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k)));
         at(statement(8).statement(1).statement(1).entry, load<uint8>(at(before_decrement, buf + k))) == at(before_decrement, load<uint8>(buf + k));
         at(before_decrement, load<uint8>(buf + k)) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k];
        };
       }
      }
     }
     have to_integer(adler) == to_integer(at(before_add, adler + at(before_decrement, buf[0]) as uint32 as uint64)) by close();
     have to_integer(sum2) == to_integer(at(before_add, sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))) by close();
     have to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) by close();
     have zlib_prefix_count(at(loop(4).entry, len), len) == (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32 by close() using { to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1); };
     have to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(to_integer(adler), at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)));
      rewrite(zlib_prefix_count(at(loop(4).entry, len), len), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum(at(loop(4).entry, buf), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(sum2) == to_integer(at(loop(4).entry, sum2)) + to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(to_integer(sum2), at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))));
      apply(zlib_canonical_weighted_sum_count_equal(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32));
      rewrite(adler_weighted_sum(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), len), zlib_prefix_count(at(loop(4).entry, len), len)), adler_weighted_sum(at(loop(4).entry, buf), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1)));
      rewrite(zlib_prefix_count(at(loop(4).entry, len), len), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64)) == to_integer(at(loop(4).entry, sum2)) + to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1)) * to_integer(at(loop(4).entry, adler)) + adler_weighted_sum(at(loop(4).entry, buf), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(adler) <= 1500000 + 255 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(to_integer(adler), at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64)));
      rewrite(zlib_prefix_count(at(loop(4).entry, len), len), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(adler + at(before_decrement, buf[0]) as uint32 as uint64) <= 1500000 + 255 * to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     }
     have to_integer(sum2) <= 10000000000 + 1504080 * to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) by {
      rewrite(to_integer(sum2), at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64))));
      rewrite(zlib_prefix_count(at(loop(4).entry, len), len), (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) as int32);
      close() using { at(before_add, to_integer(sum2 + (adler + at(before_decrement, buf[0]) as uint32 as uint64)) <= 10000000000 + 1504080 * to_integer((zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1))); };
     }
     have len <= at(before_decrement, len) by {
      have to_integer(len) <= to_integer(at(before_decrement, len)) by close() using {
       to_integer(len) == at(before_decrement, to_integer(len)) - 1;
      };
      apply(integer::uint64_to_integer_less_equal_implies_less_equal(len, at(before_decrement, len)));
     }
     have len <= at(loop(4).entry, len) by close() using { len <= at(before_decrement, len); at(before_decrement, len) <= at(loop(4).entry, len); at(loop(4).entry, len) <= 2147483647u64; };
     have to_integer(at(loop(4).entry, len) - at(before_decrement, len)) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), at(before_decrement, len)));
      have to_integer(at(loop(4).entry, len)) <= 2147483647 by close() using { at(loop(4).entry, len) <= 2147483647u64; };
      have 0 <= to_integer(at(before_decrement, len)) by close();
      rewrite(to_integer(at(loop(4).entry, len) - at(before_decrement, len)), to_integer(at(loop(4).entry, len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 2147483647, to_integer(at(before_decrement, len)), 0));
      close();
     }
     have to_integer(at(loop(4).entry, len) - len) <= to_integer(2147483647u64) by {
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), len));
      have to_integer(at(loop(4).entry, len)) <= 2147483647 by close() using { at(loop(4).entry, len) <= 2147483647u64; };
      have 0 <= to_integer(len) by close();
      rewrite(to_integer(at(loop(4).entry, len) - len), to_integer(at(loop(4).entry, len)) - to_integer(len));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 2147483647, to_integer(len), 0));
      close();
     }
     apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), at(before_decrement, len))); apply(zlib_full_prefix_pointer(at(loop(4).entry, buf), at(loop(4).entry, len), len));
     have to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) by close();
     have defined(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1) by close();
     apply(click::integer::uint8_pointer_add_associate_int32(at(loop(4).entry, buf), zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)), 1));
     have buf == at(loop(4).entry, buf) + (at(loop(4).entry, len) - len) by close() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len));
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - at(before_decrement, len)) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len));
      at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1 == at(loop(4).entry, buf) + (zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1);
      to_integer(zlib_prefix_count(at(loop(4).entry, len), len)) == to_integer(zlib_prefix_count(at(loop(4).entry, len), at(before_decrement, len)) + 1);
      at(loop(4).entry, buf) + (at(loop(4).entry, len) - len) == at(loop(4).entry, buf) + zlib_prefix_count(at(loop(4).entry, len), len);
     };
     have len <= old(len) by close() using { len <= at(before_decrement, len); at(before_decrement, len) <= old(len); old(len) <= 9223372036854775807u64; };
     have 1u64 <= at(before_decrement, len) by close();
     apply(zlib_full_prefix_advance_u64(old(buf), old(len), at(before_decrement, len), 1u64));
     have buf == old(buf) + (old(len) - len) by close() using {
      buf == at(before_decrement, buf) + 1;
      at(before_decrement, buf) == old(buf) + (old(len) - at(before_decrement, len));
      old(buf) + (old(len) - at(before_decrement, len)) + 1u64 == old(buf) + (old(len) - (at(before_decrement, len) - 1u64));
      to_integer(len) == to_integer(at(before_decrement, len) - 1u64);
     };
     have len <= 9223372036854775807u64 by close() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     have len == at(before_decrement, len - 1u64) by close();
     apply(click::separation::contains_subrange(at(before_decrement, buf), 0u64, at(before_decrement, len), 1u64, at(before_decrement, len)));
     have contains(memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]), memory(buf[0u64..len])) by {
      rewrite(buf, at(before_decrement, buf) + 1);
      rewrite(len, at(before_decrement, len - 1u64));
      apply(click::separation::contains_rebase(at(before_decrement, buf), 1u64, at(before_decrement, len)));
     }
     apply(click::separation::contains_trans(at(before_decrement, memory(buf[0u64..len])), memory(at(before_decrement, buf)[1u64..at(before_decrement, len)]), memory(buf[0u64..len])));
     apply(click::separation::viewable_restrict(at(before_decrement, memory(buf[0u64..len])), memory(buf[0u64..len])));
     have at(before_decrement, len) <= at(loop(4).entry, len) by close();
     apply(zlib_uint64_difference_bound(at(loop(4).entry, len), at(before_decrement, len), 15u64));
     have to_integer(at(loop(4).entry, len) - at(before_decrement, len)) <= 14 by {
      have to_integer(at(loop(4).entry, len)) <= 15 by close() using { at(loop(4).entry, len) <= 15u64; };
      have to_integer(1u64) <= to_integer(at(before_decrement, len)) by close() using { 1u64 <= at(before_decrement, len); };
      apply(integer::uint64_subtract_to_integer(at(loop(4).entry, len), at(before_decrement, len)));
      rewrite(to_integer(at(loop(4).entry, len) - at(before_decrement, len)), to_integer(at(loop(4).entry, len)) - to_integer(at(before_decrement, len)));
      apply(integer::subtract_le(to_integer(at(loop(4).entry, len)), 15, to_integer(at(before_decrement, len)), 1));
      close();
     }
     have to_integer(at(loop(4).entry, len) - len) == to_integer((at(loop(4).entry, len) - at(before_decrement, len)) + 1u64) by close() using {
      to_integer(len) == to_integer(at(before_decrement, len) - 1u64);
      1u64 <= at(before_decrement, len);
      at(before_decrement, len) <= at(loop(4).entry, len);
      at(loop(4).entry, len) <= 15u64;
     };
     have (at(loop(4).entry, len) - len) as uint64 == ((at(loop(4).entry, len) - at(before_decrement, len)) + 1u64) as uint64 by close() using {
      to_integer(at(loop(4).entry, len) - len) == to_integer((at(loop(4).entry, len) - at(before_decrement, len)) + 1u64);
     };
     have to_integer(len) <= 15 by close() using { len <= at(loop(4).entry, len); at(loop(4).entry, len) <= 15u64; };
     have forall (k: uint64) { k < len implies load<uint8>(buf + k) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k] } by {
      intro() {
       intro() {
        have to_integer(k) <= 15 by close() using { k < len; to_integer(len) <= 15; };
        have 1 + to_integer(k) <= 18446744073709551615 by close() using { to_integer(k) <= 15; };
        apply(integer::uint64_add_to_integer(1u64, k));
        have 1u64 + k < at(before_decrement, len) by close() using {
         k < len;
         to_integer(len) == at(before_decrement, to_integer(len)) - 1;
         to_integer(1u64 + k) == to_integer(1u64) + to_integer(k);
        };
        instantiate(forall (k: uint64) { k < at(before_decrement, len) implies at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + k))) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + k] }, 1u64 + k);
        apply(integer::uint8_pointer_add_associate_uint64(at(before_decrement, buf), 1u64, k));
        have buf + k == at(before_decrement, buf + (1u64 + k)) by {
         rewrite(buf, at(before_decrement, buf) + 1);
         close();
        }
        have load<uint8>(buf + k) == at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))) by {
         rewrite(buf + k, at(before_decrement, buf + (1u64 + k)));
         close();
        }
        have (at(loop(4).entry, len) - len) + k == (at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k) by {
         rewrite(to_integer(len), at(before_decrement, to_integer(len)) - 1);
         close();
        }
        have at(loop(4).entry, buf) + ((at(loop(4).entry, len) - len) + k) == at(loop(4).entry, buf) + ((at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k)) by {
         rewrite((at(loop(4).entry, len) - len) + k, (at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k));
         close();
        }
        have at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k] == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k)] by {
         close() using { at(loop(4).entry, buf) + ((at(loop(4).entry, len) - len) + k) == at(loop(4).entry, buf) + ((at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k)); };
        }
        rewrite(at(loop(4).entry, buf)[(at(loop(4).entry, len) - len) + k], at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k)]);
        rewrite(load<uint8>(buf + k), at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))));
        close() using { at(statement(8).statement(1).statement(1).exit, load<uint8>(at(before_decrement, buf + (1u64 + k)))) == at(loop(4).entry, buf)[(at(loop(4).entry, len) - at(before_decrement, len)) + (1u64 + k)]; };
       }
      }
     }

     have 0 <= to_integer(len); have to_integer(len) <= 18446744073709551615;
     have to_integer(len) < at(before_decrement, to_integer(len)) by close() using { to_integer(len) == at(before_decrement, to_integer(len)) - 1; };
    }
   }
  }
  step_until(assignment(adler, 39).entry);
  step_until(function.exit); close();
 }
  }
 }
}
