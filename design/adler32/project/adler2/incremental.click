// Real two-update client of the unchanged pinned library.
fn adler_incremental::incremental(bytes: &[u8], split: usize) -> u32 {
 requires bytes.len() <= 2147483647u64;
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
} by {
 apply(adler_incremental_split_defined(bytes.len(), split)) using { bytes.len() <= 2147483647u64; split <= bytes.len(); };
 apply(adler_incremental_split(bytes.len(), split)) using { bytes.len() <= 2147483647u64; split <= bytes.len(); defined((int32)(uint32)split + (int32)(uint32)(bytes.len() - split)); defined(2147483647 - (int32)(uint32)(bytes.len() - split)); };
 execute_until(assignment(__rust_mir_10, 0));
 have prefix_len == split by simp();
 have to_integer(suffix_len) == to_integer(bytes.len() - split) by simp();
 have prefix == bytes by simp();
 have suffix == bytes + split by simp();
 have state.a == 1 by simp();
 have state.b == 0 by simp();
 have to_integer((state.a as u32)) == 1 by { rewrite(state.a == 1); normalize(); }
 have to_integer((state.b as u32)) == 0 by { rewrite(state.b == 0); normalize(); }
 mark initial_seed;
 execute_until(assignment(__rust_mir_13, 0));
 have to_integer(state.a) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite(1 == at(initial_seed, to_integer((state.a as u32)))); assumption(); }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite(1 == at(initial_seed, to_integer((state.a as u32)))); rewrite(0 == at(initial_seed, to_integer((state.b as u32)))); assumption(); }
 apply(adler_u16_observation(state.a));
 apply(adler_u16_observation(state.b));
 have to_integer((state.a as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by arithmetic() using { to_integer((state.a as u32)) == to_integer(state.a); to_integer(state.a) == old(adler_spec_a_u64(bytes, split, 1)); };
 have to_integer((state.b as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by arithmetic() using { to_integer((state.b as u32)) == to_integer(state.b); to_integer(state.b) == old(adler_spec_b_u64(bytes, split, 1, 0)); };
 mark prefix_done;
 have forall (k: uint64) { to_integer(k) < to_integer(bytes.len() - split) implies suffix[k] == old((bytes + split)[k]) } by {
  intro(); intro();
  normalize();
 }
 apply(adler_spec_extensional_u64(suffix, old(bytes + split), bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))) using {
  forall (k: uint64) { to_integer(k) < to_integer(bytes.len() - split) implies suffix[k] == old((bytes + split)[k]) };
 };
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(state.a) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))) by assumption();
 have to_integer(state.b) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))) by assumption();
 have at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))))) by assumption();
 have at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))) by assumption();
 have to_integer(state.a) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)) == at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))))) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))));
  assumption();
 }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)) == at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_b_u64(bytes, split, 1, 0)) == at(prefix_done, to_integer((state.b as u32))));
  rewrite(old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))));
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
 have to_integer(state.a) == old(adler_spec_a_u64(bytes, bytes.len(), 1)) by {
  rewrite(adler_spec_a_u64(bytes, bytes.len(), 1) == adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)));
  assumption();
 }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes, bytes.len(), 1, 0) == adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)));
  assumption();
 }
 have 65536 * to_integer(state.b) + to_integer(state.a) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
  rewrite(to_integer(state.a) == old(adler_spec_a_u64(bytes, bytes.len(), 1)));
  rewrite(to_integer(state.b) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)));
  normalize();
 }
 step();
 have to_integer(__rust_mir_0) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by arithmetic() using {
  to_integer(__rust_mir_0) == 65536 * to_integer(state.b) + to_integer(state.a);
  65536 * to_integer(state.b) + to_integer(state.a) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
 };
 have forall (k: int32) { 0 <= k and k < ((bytes.len() as u32) as i32) implies bytes[k] == old(bytes[k]) } by {
  intro(); intro();
  extract(0 <= k); extract(k < ((bytes.len() as u32) as i32));
  apply(adler_bounded_signed_index(bytes.len(), k)) using { bytes.len() <= 2147483647u64; 0 <= k; k < ((bytes.len() as u32) as i32); };
  simp();
 }
 execute(); simp();
}
