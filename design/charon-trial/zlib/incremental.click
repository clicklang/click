import "canonical.click";
import "../adler2/incremental-split.click";
verifying "incremental.c";
uint64 click_zlib_incremental(uint64 seed, const uint8* buf, uint64 len, uint64 split) {
 requires zlib_seed_a(seed) <= 65520u64;
 requires zlib_seed_b(seed) <= 65520u64;
 requires len <= 2147483647u64;
 requires split <= len;
 requires buf != 0;
 requires buf + split != 0;
 views buf[0u64..len];
 ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed))));
 ensures forall (k: uint64) { k < old(len) implies old(buf)[k] == old(buf[k]) };
} by {
 have viewable(buf[0u64..len]) by simp();
 apply(zlib_seed_bounds(seed));
 apply(adler_incremental_split(len, split));
 have viewable(buf[0u64..split]) by simp();
 execute_until(assignment(prefix, 0)); step();
 apply(zlib_checksum_seed(buf, (int32)(uint32)split, prefix, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
 apply(adler_bounded_pointer_index(buf, split));
 have buf + split != 0 by assumption();
 have viewable((buf + split)[0u64..len - split]) by simp();
 apply(adler_spec_checksum_concat(buf, (int32)(uint32)split, (int32)(uint32)(len - split), to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
 have adler_spec_checksum(buf + split, (int32)(uint32)(len - split), to_integer(zlib_seed_a(prefix)), to_integer(zlib_seed_b(prefix))) == adler_spec_checksum(buf, (int32)(uint32)len, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))) by {
  rewrite(buf + split == buf + (int32)(uint32)split);
  rewrite(to_integer(zlib_seed_a(prefix)) == adler_spec_a(buf, (int32)(uint32)split, to_integer(zlib_seed_a(seed))));
  rewrite(to_integer(zlib_seed_b(prefix)) == adler_spec_b(buf, (int32)(uint32)split, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))));
  rewrite((int32)(uint32)len == (int32)(uint32)split + (int32)(uint32)(len - split));
  simp() using { adler_spec_checksum(buf, (int32)(uint32)split + (int32)(uint32)(len - split), to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed))) == adler_spec_checksum(buf + (int32)(uint32)split, (int32)(uint32)(len - split), adler_spec_a(buf, (int32)(uint32)split, to_integer(zlib_seed_a(seed))), adler_spec_b(buf, (int32)(uint32)split, to_integer(zlib_seed_a(seed)), to_integer(zlib_seed_b(seed)))); };
 }
 have adler_spec_checksum(old(buf) + split, (int32)(uint32)(len - split), to_integer(zlib_seed_a(prefix)), to_integer(zlib_seed_b(prefix))) == adler_spec_checksum(old(buf), old((int32)(uint32)len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))) by simp();
 mark before_suffix;
 execute();
 have to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))) by {
  arithmetic() using { to_integer(result) == adler_spec_checksum(old(buf) + split, (int32)(uint32)(len - split), to_integer(zlib_seed_a(at(before_suffix, prefix))), to_integer(zlib_seed_b(at(before_suffix, prefix)))); adler_spec_checksum(old(buf) + split, (int32)(uint32)(len - split), to_integer(zlib_seed_a(at(before_suffix, prefix))), to_integer(zlib_seed_b(at(before_suffix, prefix)))) == adler_spec_checksum(old(buf), old((int32)(uint32)len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))); };
 }
 simp();
}
