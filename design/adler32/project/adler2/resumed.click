import click::integer;

// Save and restore the prefix checksum before updating the unchanged suffix.
fn adler_resumed::resumed(bytes: &[u8], split: usize) -> u32 {
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
} by {
 execute_until(assignment(__rust_mir_10, 0));
 have prefix_len == split by simp();
 have to_integer(suffix_len) == to_integer(bytes.len() - split) by simp();
 have prefix == bytes by simp();
 have suffix == bytes + split by simp();
 have __rust_mir_8.a == 1 by simp();
 have __rust_mir_8.b == 0 by simp();
 have to_integer((__rust_mir_8.a as u32)) == 1 by { rewrite(__rust_mir_8.a == 1); normalize(); }
 have to_integer((__rust_mir_8.b as u32)) == 0 by { rewrite(__rust_mir_8.b == 0); normalize(); }
 mark initial_seed;
 execute_until(assignment(__rust_mir_13, 0));
 have to_integer(__rust_mir_8.a) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite(1 == at(initial_seed, to_integer((__rust_mir_8.a as u32)))); assumption(); }
 have to_integer(__rust_mir_8.b) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite(1 == at(initial_seed, to_integer((__rust_mir_8.a as u32)))); rewrite(0 == at(initial_seed, to_integer((__rust_mir_8.b as u32)))); assumption(); }
 apply(adler_u16_observation(__rust_mir_8.a));
 apply(adler_u16_observation(__rust_mir_8.b));
 have to_integer((__rust_mir_8.a as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by arithmetic() using { to_integer((__rust_mir_8.a as u32)) == to_integer(__rust_mir_8.a); to_integer(__rust_mir_8.a) == old(adler_spec_a_u64(bytes, split, 1)); };
 have to_integer((__rust_mir_8.b as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by arithmetic() using { to_integer((__rust_mir_8.b as u32)) == to_integer(__rust_mir_8.b); to_integer(__rust_mir_8.b) == old(adler_spec_b_u64(bytes, split, 1, 0)); };
 apply(uint32_less_equal_to_integer((__rust_mir_8.a as u32), 65520u32));
 have to_integer((__rust_mir_8.a as u32)) <= to_integer(65535u32) by arithmetic() using { to_integer((__rust_mir_8.a as u32)) <= to_integer(65520u32); };
 apply(uint32_to_integer_less_equal_implies_less_equal((__rust_mir_8.a as u32), 65535u32));
 apply(uint32_less_equal_to_integer((__rust_mir_8.b as u32), 65520u32));
 have to_integer((__rust_mir_8.b as u32)) <= to_integer(65535u32) by arithmetic() using { to_integer((__rust_mir_8.b as u32)) <= to_integer(65520u32); };
 apply(uint32_to_integer_less_equal_implies_less_equal((__rust_mir_8.b as u32), 65535u32));
 mark saved_state;
 apply(uint32_unpack_uint16_low((__rust_mir_8.a as u32), (__rust_mir_8.b as u32)));
 apply(uint32_unpack_uint16_high((__rust_mir_8.a as u32), (__rust_mir_8.b as u32)));
 execute_until(assignment(__rust_mir_17, 0));
 have saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)) by assumption();
 have (__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32)) by {
  rewrite((__rust_mir_14.a as u32) == (saved & 65535u32));
  rewrite(saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)));
  assumption();
 }
 have (__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32)) by {
  rewrite((__rust_mir_14.b as u32) == ((saved >> 16) & 65535u32));
  rewrite(saved == at(saved_state, ((__rust_mir_8.b as u32) << 16) | (__rust_mir_8.a as u32)));
  assumption();
 }
 have (__rust_mir_14.a as u32) <= 65520u32 by { rewrite((__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32))); assumption(); }
 have (__rust_mir_14.b as u32) <= 65520u32 by { rewrite((__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32))); assumption(); }
 have to_integer((__rust_mir_14.a as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite((__rust_mir_14.a as u32) == at(saved_state, (__rust_mir_8.a as u32))); assumption(); }
 have to_integer((__rust_mir_14.b as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite((__rust_mir_14.b as u32) == at(saved_state, (__rust_mir_8.b as u32))); assumption(); }
 mark prefix_done;
 have forall (k: uint64) { to_integer(k) < to_integer(bytes.len() - split) implies suffix[k] == old((bytes + split)[k]) } by {
  intro(); intro();
  normalize();
 }
 apply(adler_spec_extensional_u64(suffix, old(bytes + split), bytes.len() - split, to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) using {
  forall (k: uint64) { to_integer(k) < to_integer(bytes.len() - split) implies suffix[k] == old((bytes + split)[k]) };
 };
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(__rust_mir_14.a) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)))) by assumption();
 have to_integer(__rust_mir_14.b) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) by assumption();
 have at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)))) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((__rust_mir_14.a as u32))))) by assumption();
 have at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((__rust_mir_14.a as u32))), at(prefix_done, to_integer((__rust_mir_14.b as u32))))) by assumption();
 have to_integer(__rust_mir_14.a) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)) == at(prefix_done, to_integer((__rust_mir_14.a as u32))));
  rewrite(old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((__rust_mir_14.a as u32))))) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)))));
  assumption();
 }
 have to_integer(__rust_mir_14.b) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)) == at(prefix_done, to_integer((__rust_mir_14.a as u32))));
  rewrite(old(adler_spec_b_u64(bytes, split, 1, 0)) == at(prefix_done, to_integer((__rust_mir_14.b as u32))));
  rewrite(old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((__rust_mir_14.a as u32))), at(prefix_done, to_integer((__rust_mir_14.b as u32))))) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((__rust_mir_14.a as u32)), to_integer((__rust_mir_14.b as u32)))));
  assumption();
 }
 // Compose the two updates over the uint64 specification at the split.
 apply(uint64_to_integer_bounds(split));
 apply(uint64_less_equal_to_integer(split, bytes.len())) using { split <= bytes.len(); };
 apply(uint64_subtract_to_integer(bytes.len(), split)) using { to_integer(split) <= to_integer(bytes.len()); };
 apply(uint64_to_integer_bounds(bytes.len()));
 have to_integer(split) + to_integer(bytes.len() - split) <= 18446744073709551615 by arithmetic() using {
  to_integer(bytes.len() - split) == to_integer(bytes.len()) - to_integer(split);
  to_integer(bytes.len()) <= 18446744073709551615;
 };
 apply(adler_spec_a_concat_u64(bytes, split, bytes.len() - split, 1));
 apply(adler_spec_b_concat_u64(bytes, split, bytes.len() - split, 1, 0));
 have to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()) by normalize();
 have adler_spec_a_u64(bytes, bytes.len(), 1) == adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)) by {
  rewrite(adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)) == adler_spec_a_u64(bytes, split + (bytes.len() - split), 1));
  rewrite(to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()));
  normalize();
 }
 have adler_spec_b_u64(bytes, bytes.len(), 1, 0) == adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)) == adler_spec_b_u64(bytes, split + (bytes.len() - split), 1, 0));
  rewrite(to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()));
  normalize();
 }
 have to_integer(__rust_mir_14.a) == old(adler_spec_a_u64(bytes, bytes.len(), 1)) by {
  rewrite(adler_spec_a_u64(bytes, bytes.len(), 1) == adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)));
  assumption();
 }
 have to_integer(__rust_mir_14.b) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes, bytes.len(), 1, 0) == adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)));
  assumption();
 }
 have 65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
  rewrite(to_integer(__rust_mir_14.a) == old(adler_spec_a_u64(bytes, bytes.len(), 1)));
  rewrite(to_integer(__rust_mir_14.b) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)));
  normalize();
 }
 step();
 have to_integer(__rust_mir_0) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by arithmetic() using {
  to_integer(__rust_mir_0) == 65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a);
  65536 * to_integer(__rust_mir_14.b) + to_integer(__rust_mir_14.a) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
 };
 have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by simp();
 execute(); simp();
}
