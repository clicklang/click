import click::integer;

// Save and restore the prefix checksum before updating the unchanged suffix.
fn adler_resumed::resumed(bytes: &[u8], split: usize) -> u32 {
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(bytes.as_ptr(), bytes.len(), 1, 0));
} by {
 mark input_bytes;
 // Compose the two updates over the uint64 specification at the split.
 have to_integer((bytes.len()) - split) == to_integer((bytes.len())) - to_integer(split);
 have to_integer(split) + to_integer(bytes.len() - split) <= 18446744073709551615 by close() using {
  to_integer(bytes.len() - split) == to_integer(bytes.len()) - to_integer(split);
  to_integer(bytes.len()) <= 18446744073709551615;
 };
 apply(adler_spec_a_concat_u64(bytes.as_ptr(), split, bytes.len() - split, 1));
 apply(adler_spec_b_concat_u64(bytes.as_ptr(), split, bytes.len() - split, 1, 0));
 have to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()) by close();
 have adler_spec_a_u64(bytes.as_ptr(), bytes.len(), 1) == adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, adler_spec_a_u64(bytes.as_ptr(), split, 1)) by {
  rewrite(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, adler_spec_a_u64(bytes.as_ptr(), split, 1)), adler_spec_a_u64(bytes.as_ptr(), split + (bytes.len() - split), 1));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  close();
 }
 have adler_spec_b_u64(bytes.as_ptr(), bytes.len(), 1, 0) == adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, adler_spec_a_u64(bytes.as_ptr(), split, 1), adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, adler_spec_a_u64(bytes.as_ptr(), split, 1), adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)), adler_spec_b_u64(bytes.as_ptr(), split + (bytes.len() - split), 1, 0));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  close();
 }
 have old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), 1)) == old(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)))) by close();
 have old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), 1, 0)) == old(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)), old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)))) by close();
 step_until(statement(2).entry);
 have prefix.len() == split by close();
 have to_integer(suffix.len()) == to_integer(bytes.len() - split) by close();
 have prefix == bytes.as_ptr() by close();
 have suffix == bytes.as_ptr() + split by close();
 // Read the two uint16 fields of the active accumulator.
 have load<uint16>(state) == 1 by close();
 have load<uint16>(state + 2u64) == 0 by close();
 have to_integer((load<uint16>(state) as u32)) == 1 by { rewrite(load<uint16>(state), 1); close(); }
 have to_integer((load<uint16>(state + 2u64) as u32)) == 0 by { rewrite(load<uint16>(state + 2u64), 0); close(); }
 mark initial_seed;
     have forall (k: uint64) { k < split implies prefix[k] == old(bytes[k]) } by {
      intro() {
       intro() {
        apply(integer::uint64_less_than_less_equal_transitive(k, split, bytes.len()));
        have prefix + k == bytes.as_ptr() + k by { rewrite(prefix, bytes.as_ptr()); close(); }
        have k < old(bytes.len()) by close();
        have bytes.as_ptr() + k == old(bytes.as_ptr()) + k by { rewrite(bytes.as_ptr(), old(bytes.as_ptr())); close(); }
        have at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]) by close();
        have at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(1).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(1)); }
        have at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
         at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(2).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(2)); }
        have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(3).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(3)); }
        have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(4).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(4)); }
        have at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(6).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(6)); }
        have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(23).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(23)); }
        have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        have at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        have separate(region(26).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(26)); }
        have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
         at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
        };
        rewrite(prefix + k, bytes.as_ptr() + k);
        rewrite(bytes.as_ptr() + k, old(bytes.as_ptr()) + k);
        have load<uint8>(old(bytes.as_ptr()) + k) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
        close() using {
         load<uint8>(old(bytes.as_ptr()) + k) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k));
         at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
         at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]);
        };
       }
      }
     }
 apply(adler_spec_extensional_u64(prefix, old(bytes.as_ptr()), split, 1, 0));
 step_until(statement(3).entry);
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes.as_ptr(), split, 1)) by { rewrite(1, at(initial_seed, to_integer((load<uint16>(state) as u32)))); close(); }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)) by { rewrite(1, at(initial_seed, to_integer((load<uint16>(state) as u32)))); rewrite(0, at(initial_seed, to_integer((load<uint16>(state + 2u64) as u32)))); close(); }
 apply(adler_u16_observation(load<uint16>(state)));
 apply(adler_u16_observation(load<uint16>(state + 2u64)));
 have to_integer((load<uint16>(state) as u32)) == old(adler_spec_a_u64(bytes.as_ptr(), split, 1)) by close() using { to_integer((load<uint16>(state) as u32)) == to_integer(load<uint16>(state)); to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes.as_ptr(), split, 1)); };
 have to_integer((load<uint16>(state + 2u64) as u32)) == old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)) by close() using { to_integer((load<uint16>(state + 2u64) as u32)) == to_integer(load<uint16>(state + 2u64)); to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)); };
 have to_integer((load<uint16>(state) as u32)) <= to_integer(65535u32) by close() using { to_integer((load<uint16>(state) as u32)) <= to_integer(65520u32); };
 apply(integer::uint32_to_integer_less_equal_implies_less_equal((load<uint16>(state) as u32), 65535u32));
 have to_integer((load<uint16>(state + 2u64) as u32)) <= to_integer(65535u32) by close() using { to_integer((load<uint16>(state + 2u64) as u32)) <= to_integer(65520u32); };
 apply(integer::uint32_to_integer_less_equal_implies_less_equal((load<uint16>(state + 2u64) as u32), 65535u32));
 mark saved_state;
 apply(integer::uint32_unpack_uint16_low((load<uint16>(state) as u32), (load<uint16>(state + 2u64) as u32)));
 apply(integer::uint32_unpack_uint16_high((load<uint16>(state) as u32), (load<uint16>(state + 2u64) as u32)));
 step_until(statement(5).entry);
 have saved == at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)) by close();
 have (load<uint16>(state) as u32) == at(saved_state, (load<uint16>(state) as u32)) by {
  rewrite((load<uint16>(state) as u32), (saved & 65535u32));
  rewrite(saved, at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)));
  close();
 }
 have (load<uint16>(state + 2u64) as u32) == at(saved_state, (load<uint16>(state + 2u64) as u32)) by {
  rewrite((load<uint16>(state + 2u64) as u32), ((saved >> 16) & 65535u32));
  rewrite(saved, at(saved_state, ((load<uint16>(state + 2u64) as u32) << 16) | (load<uint16>(state) as u32)));
  close();
 }
 have (load<uint16>(state) as u32) <= 65520u32 by { rewrite((load<uint16>(state) as u32), at(saved_state, (load<uint16>(state) as u32))); close(); }
 have (load<uint16>(state + 2u64) as u32) <= 65520u32 by { rewrite((load<uint16>(state + 2u64) as u32), at(saved_state, (load<uint16>(state + 2u64) as u32))); close(); }
 have to_integer((load<uint16>(state) as u32)) == old(adler_spec_a_u64(bytes.as_ptr(), split, 1)) by { rewrite((load<uint16>(state) as u32), at(saved_state, (load<uint16>(state) as u32))); close(); }
 have to_integer((load<uint16>(state + 2u64) as u32)) == old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)) by { rewrite((load<uint16>(state + 2u64) as u32), at(saved_state, (load<uint16>(state + 2u64) as u32))); close(); }
 mark prefix_done;
 have forall (k: uint64) { k < bytes.len() - split implies suffix[k] == old((bytes.as_ptr() + split)[k]) } by {
  intro() {
   intro() {
    have k < old(bytes.len() - split) by close();
    have suffix == bytes.as_ptr() + split by close();
    have bytes.as_ptr() + split == old(bytes.as_ptr() + split) by close();
    have suffix + k == (bytes.as_ptr() + split) + k by { rewrite(suffix, bytes.as_ptr() + split); close(); }
    have (bytes.as_ptr() + split) + k == old(bytes.as_ptr() + split) + k by { rewrite(bytes.as_ptr() + split, old(bytes.as_ptr() + split)); close(); }
    have at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) == old((bytes.as_ptr() + split)[k]) by close();
    have at(region(1).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(1).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(1)); }
    have at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(1).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(2).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(2).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(2)); }
    have at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(2).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(1).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(3).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(3).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(3)); }
    have at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(3).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(2).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(4).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(4).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(4)); }
    have at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(4).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(3).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(6).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(6).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(6)); }
    have at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(6).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(4).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(23).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(23).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(23)); }
    have at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(23).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(6).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(26).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(26).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(26)); }
    have at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(26).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(23).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(37).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(37).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(37).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(37)); }
    have at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(37).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(37).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(26).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(48).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(48).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(48).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(48)); }
    have at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(48).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(48).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(37).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    have at(region(53).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    have separate(region(53).footprint, at(input_bytes, memory((bytes.as_ptr() + split)[k]))) by close();
    have at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(53).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) by { preserve(at(input_bytes, memory((bytes.as_ptr() + split)[k])), region(53)); }
    have at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) by close() using {
     at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(53).entry, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(53).entry, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(48).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
    };
    rewrite(suffix + k, (bytes.as_ptr() + split) + k);
    rewrite((bytes.as_ptr() + split) + k, old(bytes.as_ptr() + split) + k);
    have load<uint8>(old(bytes.as_ptr() + split) + k) == at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) by close();
    close() using {
     load<uint8>(old(bytes.as_ptr() + split) + k) == at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(region(53).exit, load<uint8>(old(bytes.as_ptr() + split) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k));
     at(input_bytes, load<uint8>(old(bytes.as_ptr() + split) + k)) == old((bytes.as_ptr() + split)[k]);
    };
   }
  }
 }
 apply(adler_spec_extensional_u64(suffix, old(bytes.as_ptr() + split), bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32))));
 step_until(statement(6).call(0).entry);
 have to_integer(load<uint16>(state)) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))) by close();
 have to_integer(load<uint16>(state + 2u64)) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))) by close();
 have at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))) == old(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))))) by close();
 have at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))) == old(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))))) by close();
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)))) by {
  rewrite(old(adler_spec_a_u64(bytes.as_ptr(), split, 1)), at(prefix_done, to_integer((load<uint16>(state) as u32))));
  rewrite(old(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))))), at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)))));
  close();
 }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)), old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)))) by {
  rewrite(old(adler_spec_a_u64(bytes.as_ptr(), split, 1)), at(prefix_done, to_integer((load<uint16>(state) as u32))));
  rewrite(old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))));
  rewrite(old(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, at(prefix_done, to_integer((load<uint16>(state) as u32))), at(prefix_done, to_integer((load<uint16>(state + 2u64) as u32))))), at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((load<uint16>(state) as u32)), to_integer((load<uint16>(state + 2u64) as u32)))));
  close();
 }
 have to_integer(load<uint16>(state)) == old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), 1)) by {
  rewrite(old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), 1)), old(adler_spec_a_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)))));
  close();
 }
 have to_integer(load<uint16>(state + 2u64)) == old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), 1, 0)) by {
  rewrite(old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), 1, 0)), old(adler_spec_b_u64(bytes.as_ptr() + split, bytes.len() - split, old(adler_spec_a_u64(bytes.as_ptr(), split, 1)), old(adler_spec_b_u64(bytes.as_ptr(), split, 1, 0)))));
  close();
 }
 have 65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state)) == old(adler_spec_checksum_u64(bytes.as_ptr(), bytes.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(bytes.as_ptr(), bytes.len(), 1, 0));
  rewrite(to_integer(load<uint16>(state)), old(adler_spec_a_u64(bytes.as_ptr(), bytes.len(), 1)));
  rewrite(to_integer(load<uint16>(state + 2u64)), old(adler_spec_b_u64(bytes.as_ptr(), bytes.len(), 1, 0)));
  close();
 }
 step();
 have to_integer(statement(6).call(0).result) == 65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state)) by close();
 have to_integer(statement(6).call(0).result) == old(adler_spec_checksum_u64(bytes.as_ptr(), bytes.len(), 1, 0)) by {
  rewrite(to_integer(statement(6).call(0).result), 65536 * to_integer(load<uint16>(state + 2u64)) + to_integer(load<uint16>(state)));
  close();
 }
 have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by {
  intro() {
   intro() {
    have k < old(bytes.len()) by close();
    have bytes.as_ptr() == old(bytes.as_ptr()) by close();
    have bytes.as_ptr() + k == old(bytes.as_ptr()) + k by { rewrite(bytes.as_ptr(), old(bytes.as_ptr())); close(); }
    have at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]) by close();
    have at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(1).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(1)); }
    have at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(1).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
     at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(2).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(2)); }
    have at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(2).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(1).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(3).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(3)); }
    have at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(3).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(2).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(4).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(4)); }
    have at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(4).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(3).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(6).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(6)); }
    have at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(6).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(4).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(23).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(23)); }
    have at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(23).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(6).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(26).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(26)); }
    have at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(26).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(23).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(37).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(37).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(37).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(37)); }
    have at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(37).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(37).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(26).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(48).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(48).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(48).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(48)); }
    have at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(48).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(48).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(37).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(53).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(53).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(53).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(53)); }
    have at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(53).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(53).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(48).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    have at(region(64).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    have separate(region(64).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(64).entry, load<uint8>(old(bytes.as_ptr()) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(64)); }
    have at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) by close() using {
     at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(64).entry, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(64).entry, load<uint8>(old(bytes.as_ptr()) + k)) == at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(53).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
    };
    rewrite(bytes.as_ptr() + k, old(bytes.as_ptr()) + k);
    have load<uint8>(old(bytes.as_ptr()) + k) == at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k)) by close();
    close() using {
     load<uint8>(old(bytes.as_ptr()) + k) == at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k));
     at(region(64).exit, load<uint8>(old(bytes.as_ptr()) + k)) == at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k));
     at(input_bytes, load<uint8>(old(bytes.as_ptr()) + k)) == old(bytes[k]);
    };
   }
  }
 }
 step_until(function.exit);
 close() using { forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) }; };
 close() using { to_integer(statement(6).call(0).result) == old(adler_spec_checksum_u64(bytes.as_ptr(), bytes.len(), 1, 0)); };
}
