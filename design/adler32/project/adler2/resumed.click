import click::integer;

// Save and restore the prefix checksum before updating the unchanged suffix.
fn adler_resumed::resumed(bytes: &[u8], split: usize) -> u32 {
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
} by {
 step_until(statement(2).entry);
 have prefix.len() == split by solve();
 have to_integer(suffix.len()) == to_integer(bytes.len() - split) by solve();
 have prefix == bytes by solve();
 have suffix == bytes + split by solve();
 // Read the two uint16 fields of the active accumulator.
 have load<uint16>(state) == 1 by solve();
 have load<uint16>(state + 2u64) == 0 by solve();
 have to_integer((load<uint16>(state) as u32)) == 1 by { rewrite(load<uint16>(state), 1); normalize(); }
 have to_integer((load<uint16>(state + 2u64) as u32)) == 0 by { rewrite(load<uint16>(state + 2u64), 0); normalize(); }
 mark initial_seed;
 step_until(statement(3).entry);
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite(1, at(initial_seed, to_integer((load<uint16>(state) as u32)))); known(); }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite(1, at(initial_seed, to_integer((load<uint16>(state) as u32)))); rewrite(0, at(initial_seed, to_integer((load<uint16>(state + 2u64) as u32)))); known(); }
 apply(adler_u16_observation(load<uint16>(state)));
 apply(adler_u16_observation(load<uint16>(state + 2u64)));
 have to_integer((load<uint16>(state) as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by close() using { to_integer((load<uint16>(state) as u32)) == to_integer(load<uint16>(state)); to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes, split, 1)); };
 have to_integer((load<uint16>(state + 2u64) as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by close() using { to_integer((load<uint16>(state + 2u64) as u32)) == to_integer(load<uint16>(state + 2u64)); to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes, split, 1, 0)); };
 have to_integer((load<uint16>(state) as u32)) <= to_integer(65535u32) by close() using { to_integer((load<uint16>(state) as u32)) <= to_integer(65520u32); };
 apply(integer::uint32_to_integer_less_equal_implies_less_equal((load<uint16>(state) as u32), 65535u32));
 have to_integer((load<uint16>(state + 2u64) as u32)) <= to_integer(65535u32) by close() using { to_integer((load<uint16>(state + 2u64) as u32)) <= to_integer(65520u32); };
 apply(integer::uint32_to_integer_less_equal_implies_less_equal((load<uint16>(state + 2u64) as u32), 65535u32));
 mark saved_state;
 apply(integer::uint32_unpack_uint16_low((load<uint16>(state) as u32), (load<uint16>(state + 2u64) as u32)));
 apply(integer::uint32_unpack_uint16_high((load<uint16>(state) as u32), (load<uint16>(state + 2u64) as u32)));
 step_until(statement(5).entry);
 have saved == at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)) by known();
 have (load<uint16>(state) as u32) == at(saved_state, (load<uint16>(state) as u32)) by {
  rewrite((load<uint16>(state) as u32), (saved & 65535u32));
  rewrite(saved, at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)));
  known();
 }
 have (load<uint16>(state + 2u64) as u32) == at(saved_state, (load<uint16>(state + 2u64) as u32)) by {
  rewrite((load<uint16>(state + 2u64) as u32), ((saved >> 16) & 65535u32));
  rewrite(saved, at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)));
  known();
 }
 have (load<uint16>(state) as u32) <= 65520u32 by { rewrite((load<uint16>(state) as u32), at(saved_state, (load<uint16>(state) as u32))); known(); }
 have (load<uint16>(state + 2u64) as u32) <= 65520u32 by { rewrite((load<uint16>(state + 2u64) as u32), at(saved_state, (load<uint16>(state + 2u64) as u32))); known(); }
 have to_integer((load<uint16>(state) as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite((load<uint16>(state) as u32), at(saved_state, (load<uint16>(state) as u32))); known(); }
 have to_integer((load<uint16>(state + 2u64) as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite((load<uint16>(state + 2u64) as u32), at(saved_state, (load<uint16>(state + 2u64) as u32))); known(); }
 mark prefix_done;
 have forall (k: uint64) { to_integer(k) < to_integer(bytes.len() - split) implies suffix[k] == old((bytes + split)[k]) } by {
  intro(); intro();
  normalize();
 }
 apply(adler_spec_extensional_u64(suffix, old(bytes + split), bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32))));
 step_until(statement(6).call(0).entry);
 have to_integer(load<uint16>(state)) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))) by known();
 have to_integer(load<uint16>(state + 2u64)) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))) by known();
 have at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))))) by known();
 have at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))))) by known();
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)), at(prefix_done, to_integer((load<uint16>(state) as u32))));
  rewrite(old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))))), at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))));
  known();
 }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)), at(prefix_done, to_integer((load<uint16>(state) as u32))));
  rewrite(old(adler_spec_b_u64(bytes, split, 1, 0)), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))));
  rewrite(old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))))), at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))));
  known();
 }
 // Compose the two updates over the uint64 specification at the split.
 apply(integer::uint64_subtract_to_integer(bytes.len(), split));
 have to_integer(split) + to_integer(bytes.len() - split) <= 18446744073709551615 by close() using {
  to_integer(bytes.len() - split) == to_integer(bytes.len()) - to_integer(split);
  to_integer(bytes.len()) <= 18446744073709551615;
 };
 apply(adler_spec_a_concat_u64(bytes, split, bytes.len() - split, 1));
 apply(adler_spec_b_concat_u64(bytes, split, bytes.len() - split, 1, 0));
 have to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()) by normalize();
 have adler_spec_a_u64(bytes, bytes.len(), 1) == adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)) by {
  rewrite(adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)), adler_spec_a_u64(bytes, split + (bytes.len() - split), 1));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  normalize();
 }
 have adler_spec_b_u64(bytes, bytes.len(), 1, 0) == adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)), adler_spec_b_u64(bytes, split + (bytes.len() - split), 1, 0));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  normalize();
 }
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes, bytes.len(), 1)) by {
  rewrite(adler_spec_a_u64(bytes, bytes.len(), 1), adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)));
  known();
 }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes, bytes.len(), 1, 0), adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)));
  known();
 }
 have 65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state)) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
  rewrite(to_integer(load<uint16>(state)), old(adler_spec_a_u64(bytes, bytes.len(), 1)));
  rewrite(to_integer(load<uint16>(state + 2u64)), old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)));
  normalize();
 }
 step();
 have to_integer(statement(6).call(0).result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by close() using {
  to_integer(statement(6).call(0).result) == 65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state));
  65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state)) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
 };
 have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by solve();
}
