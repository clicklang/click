import "canonical.click";
verifying "incremental.c";
uint64 click_zlib_incremental(uint64 seed, const uint8* buf, uint64 len, uint64 split) {
 requires zlib_seed_a(seed) <= 65520u64;
 requires zlib_seed_b(seed) <= 65520u64;
 requires split <= len;
 requires buf != 0;
 requires buf + split != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed))));
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
 have viewable(buf[0u64..len]) by simp();
 apply(zlib_seed_bounds(seed));
 have viewable(buf[0u64..split]) by simp();
 execute_until(assignment(prefix, 0)); step();
 apply(zlib_checksum_seed_u64(buf, split, prefix, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
 have buf + split != 0 by assumption();
 have viewable((buf + split)[0u64..len - split]) by simp();
 have to_integer(len - split) == to_integer(len) - to_integer(split) by auto();
 have to_integer(split) + to_integer(len - split) <= 18446744073709551615 by arithmetic() using {
  to_integer(len - split) == to_integer(len) - to_integer(split);
  to_integer(len) <= 18446744073709551615;
 };
 apply(adler_spec_checksum_concat_u64(buf, split, len - split, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
 have to_integer(split + (len - split)) == to_integer(len) by normalize();
 have adler_spec_checksum_u64(buf + split, len - split, to_integer(zlib_seed_a(prefix)), to_integer(zlib_seed_b(prefix))) == adler_spec_checksum_u64(buf, len, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))) by {
  rewrite(to_integer(zlib_seed_a(prefix)) == adler_spec_a_u64(buf, split, to_integer(zlib_seed_a(seed))));
  rewrite(to_integer(zlib_seed_b(prefix)) == adler_spec_b_u64(buf, split, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
  rewrite(adler_spec_checksum_u64(buf + split, len - split, adler_spec_a_u64(buf, split, to_integer(zlib_seed_a(seed))), adler_spec_b_u64(buf, split, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed)))) == adler_spec_checksum_u64(buf, split + (len - split), to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
  rewrite(to_integer(split + (len - split)) == to_integer(len));
  normalize();
 }
 mark before_suffix;
 execute();
 have to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))) by {
  arithmetic() using { to_integer(result) == adler_spec_checksum_u64(old(buf) + split, len - split, to_integer(zlib_seed_a(at(before_suffix, prefix))), to_integer(zlib_seed_b(at(before_suffix, prefix)))); adler_spec_checksum_u64(old(buf) + split, len - split, to_integer(zlib_seed_a(at(before_suffix, prefix))), to_integer(zlib_seed_b(at(before_suffix, prefix)))) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))); };
 }
 simp();
}
