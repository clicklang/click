import click::integer;

// Real two-update client of the unchanged pinned library.
fn adler_incremental::incremental(bytes: &[u8], split: usize) -> u32 {
 requires split <= bytes.len();
 views *bytes;
 ensures forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
} by {
 mark input_bytes;
 // Compose the two updates over the uint64 specification at the split.
 have to_integer((bytes.len()) - split) == to_integer((bytes.len())) - to_integer(split);
 have to_integer(split) + to_integer(bytes.len() - split) <= 18446744073709551615 by close() using {
  to_integer(bytes.len() - split) == to_integer(bytes.len()) - to_integer(split);
  to_integer(bytes.len()) <= 18446744073709551615;
 };
 apply(adler_spec_a_concat_u64(bytes, split, bytes.len() - split, 1));
 apply(adler_spec_b_concat_u64(bytes, split, bytes.len() - split, 1, 0));
 have to_integer(split + (bytes.len() - split)) == to_integer(bytes.len()) by close();
 have adler_spec_a_u64(bytes, bytes.len(), 1) == adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)) by {
  rewrite(adler_spec_a_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1)), adler_spec_a_u64(bytes, split + (bytes.len() - split), 1));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  close();
 }
 have adler_spec_b_u64(bytes, bytes.len(), 1, 0) == adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)) by {
  rewrite(adler_spec_b_u64(bytes + split, bytes.len() - split, adler_spec_a_u64(bytes, split, 1), adler_spec_b_u64(bytes, split, 1, 0)), adler_spec_b_u64(bytes, split + (bytes.len() - split), 1, 0));
  rewrite(to_integer(split + (bytes.len() - split)), to_integer(bytes.len()));
  close();
 }
 have old(adler_spec_a_u64(bytes, bytes.len(), 1)) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))) by close();
 have old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))) by close();
 step_until(statement(2).call(0).entry);
 have prefix.len() == split by close();
 have to_integer(suffix.len()) == to_integer(bytes.len() - split) by close();
 have prefix == bytes by close();
 have suffix == bytes + split by close();
 have state.a == 1 by close();
 have state.b == 0 by close();
 have to_integer((state.a as u32)) == 1 by { rewrite(state.a, 1); close(); }
 have to_integer((state.b as u32)) == 0 by { rewrite(state.b, 0); close(); }
 mark initial_seed;
     have forall (k: uint64) { k < split implies prefix[k] == old(bytes[k]) } by {
      intro() {
       intro() {
        apply(integer::uint64_less_than_less_equal_transitive(k, split, bytes.len()));
        have prefix + k == bytes + k by { rewrite(prefix, bytes); close(); }
        have k < old(bytes.len()) by close();
        have bytes + k == old(bytes) + k by { rewrite(bytes, old(bytes)); close(); }
        have at(input_bytes, load<uint8>(old(bytes) + k)) == old(bytes[k]) by close();
        have at(region(1).entry, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close();
        have separate(region(1).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(1).exit, load<uint8>(old(bytes) + k)) == at(region(1).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(1)); }
        have at(region(1).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(1).exit, load<uint8>(old(bytes) + k)) == at(region(1).entry, load<uint8>(old(bytes) + k));
         at(region(1).entry, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
         at(input_bytes, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        have at(region(2).entry, load<uint8>(old(bytes) + k)) == at(region(1).exit, load<uint8>(old(bytes) + k)) by close();
        have separate(region(2).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(2).exit, load<uint8>(old(bytes) + k)) == at(region(2).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(2)); }
        have at(region(2).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(2).exit, load<uint8>(old(bytes) + k)) == at(region(2).entry, load<uint8>(old(bytes) + k));
         at(region(2).entry, load<uint8>(old(bytes) + k)) == at(region(1).exit, load<uint8>(old(bytes) + k));
         at(region(1).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        have at(region(3).entry, load<uint8>(old(bytes) + k)) == at(region(2).exit, load<uint8>(old(bytes) + k)) by close();
        have separate(region(3).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(3).exit, load<uint8>(old(bytes) + k)) == at(region(3).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(3)); }
        have at(region(3).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(3).exit, load<uint8>(old(bytes) + k)) == at(region(3).entry, load<uint8>(old(bytes) + k));
         at(region(3).entry, load<uint8>(old(bytes) + k)) == at(region(2).exit, load<uint8>(old(bytes) + k));
         at(region(2).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        have at(region(4).entry, load<uint8>(old(bytes) + k)) == at(region(3).exit, load<uint8>(old(bytes) + k)) by close();
        have separate(region(4).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(4).exit, load<uint8>(old(bytes) + k)) == at(region(4).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(4)); }
        have at(region(4).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(4).exit, load<uint8>(old(bytes) + k)) == at(region(4).entry, load<uint8>(old(bytes) + k));
         at(region(4).entry, load<uint8>(old(bytes) + k)) == at(region(3).exit, load<uint8>(old(bytes) + k));
         at(region(3).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        have at(region(21).entry, load<uint8>(old(bytes) + k)) == at(region(4).exit, load<uint8>(old(bytes) + k)) by close();
        have separate(region(21).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(21).exit, load<uint8>(old(bytes) + k)) == at(region(21).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(21)); }
        have at(region(21).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(21).exit, load<uint8>(old(bytes) + k)) == at(region(21).entry, load<uint8>(old(bytes) + k));
         at(region(21).entry, load<uint8>(old(bytes) + k)) == at(region(4).exit, load<uint8>(old(bytes) + k));
         at(region(4).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        have at(region(24).entry, load<uint8>(old(bytes) + k)) == at(region(21).exit, load<uint8>(old(bytes) + k)) by close();
        have separate(region(24).footprint, at(input_bytes, memory(bytes[k]))) by close();
        have at(region(24).exit, load<uint8>(old(bytes) + k)) == at(region(24).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(24)); }
        have at(region(24).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
         at(region(24).exit, load<uint8>(old(bytes) + k)) == at(region(24).entry, load<uint8>(old(bytes) + k));
         at(region(24).entry, load<uint8>(old(bytes) + k)) == at(region(21).exit, load<uint8>(old(bytes) + k));
         at(region(21).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
        };
        rewrite(prefix + k, bytes + k);
        rewrite(bytes + k, old(bytes) + k);
        have load<uint8>(old(bytes) + k) == at(region(24).exit, load<uint8>(old(bytes) + k)) by close();
        close() using {
         load<uint8>(old(bytes) + k) == at(region(24).exit, load<uint8>(old(bytes) + k));
         at(region(24).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
         at(input_bytes, load<uint8>(old(bytes) + k)) == old(bytes[k]);
        };
       }
      }
     }
 apply(adler_spec_extensional_u64(prefix, old(bytes), split, 1, 0));
 step_until(statement(3).call(0).entry);
 have to_integer(state.a) == old(adler_spec_a_u64(bytes, split, 1)) by { rewrite(1, at(initial_seed, to_integer((state.a as u32)))); close(); }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes, split, 1, 0)) by { rewrite(1, at(initial_seed, to_integer((state.a as u32)))); rewrite(0, at(initial_seed, to_integer((state.b as u32)))); close(); }
 apply(adler_u16_observation(state.a));
 apply(adler_u16_observation(state.b));
 have to_integer((state.a as u32)) == old(adler_spec_a_u64(bytes, split, 1)) by close() using { to_integer((state.a as u32)) == to_integer(state.a); to_integer(state.a) == old(adler_spec_a_u64(bytes, split, 1)); };
 have to_integer((state.b as u32)) == old(adler_spec_b_u64(bytes, split, 1, 0)) by close() using { to_integer((state.b as u32)) == to_integer(state.b); to_integer(state.b) == old(adler_spec_b_u64(bytes, split, 1, 0)); };
 mark prefix_done;
 have forall (k: uint64) { k < bytes.len() - split implies suffix[k] == old((bytes + split)[k]) } by {
  intro() {
   intro() {
    have k < old(bytes.len() - split) by close();
    have suffix == bytes + split by close();
    have bytes + split == old(bytes + split) by close();
    have suffix + k == (bytes + split) + k by { rewrite(suffix, bytes + split); close(); }
    have (bytes + split) + k == old(bytes + split) + k by { rewrite(bytes + split, old(bytes + split)); close(); }
    have at(input_bytes, load<uint8>(old(bytes + split) + k)) == old((bytes + split)[k]) by close();
    have at(region(1).entry, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(1).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(1).exit, load<uint8>(old(bytes + split) + k)) == at(region(1).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(1)); }
    have at(region(1).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(1).exit, load<uint8>(old(bytes + split) + k)) == at(region(1).entry, load<uint8>(old(bytes + split) + k));
     at(region(1).entry, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
     at(input_bytes, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(2).entry, load<uint8>(old(bytes + split) + k)) == at(region(1).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(2).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(2).exit, load<uint8>(old(bytes + split) + k)) == at(region(2).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(2)); }
    have at(region(2).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(2).exit, load<uint8>(old(bytes + split) + k)) == at(region(2).entry, load<uint8>(old(bytes + split) + k));
     at(region(2).entry, load<uint8>(old(bytes + split) + k)) == at(region(1).exit, load<uint8>(old(bytes + split) + k));
     at(region(1).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(3).entry, load<uint8>(old(bytes + split) + k)) == at(region(2).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(3).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(3).exit, load<uint8>(old(bytes + split) + k)) == at(region(3).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(3)); }
    have at(region(3).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(3).exit, load<uint8>(old(bytes + split) + k)) == at(region(3).entry, load<uint8>(old(bytes + split) + k));
     at(region(3).entry, load<uint8>(old(bytes + split) + k)) == at(region(2).exit, load<uint8>(old(bytes + split) + k));
     at(region(2).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(4).entry, load<uint8>(old(bytes + split) + k)) == at(region(3).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(4).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(4).exit, load<uint8>(old(bytes + split) + k)) == at(region(4).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(4)); }
    have at(region(4).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(4).exit, load<uint8>(old(bytes + split) + k)) == at(region(4).entry, load<uint8>(old(bytes + split) + k));
     at(region(4).entry, load<uint8>(old(bytes + split) + k)) == at(region(3).exit, load<uint8>(old(bytes + split) + k));
     at(region(3).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(21).entry, load<uint8>(old(bytes + split) + k)) == at(region(4).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(21).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(21).exit, load<uint8>(old(bytes + split) + k)) == at(region(21).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(21)); }
    have at(region(21).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(21).exit, load<uint8>(old(bytes + split) + k)) == at(region(21).entry, load<uint8>(old(bytes + split) + k));
     at(region(21).entry, load<uint8>(old(bytes + split) + k)) == at(region(4).exit, load<uint8>(old(bytes + split) + k));
     at(region(4).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(24).entry, load<uint8>(old(bytes + split) + k)) == at(region(21).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(24).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(24).exit, load<uint8>(old(bytes + split) + k)) == at(region(24).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(24)); }
    have at(region(24).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(24).exit, load<uint8>(old(bytes + split) + k)) == at(region(24).entry, load<uint8>(old(bytes + split) + k));
     at(region(24).entry, load<uint8>(old(bytes + split) + k)) == at(region(21).exit, load<uint8>(old(bytes + split) + k));
     at(region(21).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    have at(region(35).entry, load<uint8>(old(bytes + split) + k)) == at(region(24).exit, load<uint8>(old(bytes + split) + k)) by close();
    have separate(region(35).footprint, at(input_bytes, memory((bytes + split)[k]))) by close();
    have at(region(35).exit, load<uint8>(old(bytes + split) + k)) == at(region(35).entry, load<uint8>(old(bytes + split) + k)) by { preserve(at(input_bytes, memory((bytes + split)[k])), region(35)); }
    have at(region(35).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k)) by close() using {
     at(region(35).exit, load<uint8>(old(bytes + split) + k)) == at(region(35).entry, load<uint8>(old(bytes + split) + k));
     at(region(35).entry, load<uint8>(old(bytes + split) + k)) == at(region(24).exit, load<uint8>(old(bytes + split) + k));
     at(region(24).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
    };
    rewrite(suffix + k, (bytes + split) + k);
    rewrite((bytes + split) + k, old(bytes + split) + k);
    have load<uint8>(old(bytes + split) + k) == at(region(35).exit, load<uint8>(old(bytes + split) + k)) by close();
    close() using {
     load<uint8>(old(bytes + split) + k) == at(region(35).exit, load<uint8>(old(bytes + split) + k));
     at(region(35).exit, load<uint8>(old(bytes + split) + k)) == at(input_bytes, load<uint8>(old(bytes + split) + k));
     at(input_bytes, load<uint8>(old(bytes + split) + k)) == old((bytes + split)[k]);
    };
   }
  }
 }
 apply(adler_spec_extensional_u64(suffix, old(bytes + split), bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32))));
 step_until(statement(4).call(0).entry);
 have to_integer(state.a) == at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))) by close();
 have to_integer(state.b) == at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))) by close();
 have at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))))) by close();
 have at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))) by close();
 have to_integer(state.a) == old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)), at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_a_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))))), at(prefix_done, adler_spec_a_u64(suffix, bytes.len() - split, to_integer((state.a as u32)))));
  close();
 }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))) by {
  rewrite(old(adler_spec_a_u64(bytes, split, 1)), at(prefix_done, to_integer((state.a as u32))));
  rewrite(old(adler_spec_b_u64(bytes, split, 1, 0)), at(prefix_done, to_integer((state.b as u32))));
  rewrite(old(adler_spec_b_u64(bytes + split, bytes.len() - split, at(prefix_done, to_integer((state.a as u32))), at(prefix_done, to_integer((state.b as u32))))), at(prefix_done, adler_spec_b_u64(suffix, bytes.len() - split, to_integer((state.a as u32)), to_integer((state.b as u32)))));
  close();
 }
 have to_integer(state.a) == old(adler_spec_a_u64(bytes, bytes.len(), 1)) by {
  rewrite(old(adler_spec_a_u64(bytes, bytes.len(), 1)), old(adler_spec_a_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)))));
  close();
 }
 have to_integer(state.b) == old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)) by {
  rewrite(old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)), old(adler_spec_b_u64(bytes + split, bytes.len() - split, old(adler_spec_a_u64(bytes, split, 1)), old(adler_spec_b_u64(bytes, split, 1, 0)))));
  close();
 }
 have 65536 * to_integer(state.b) + to_integer(state.a) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0));
  rewrite(to_integer(state.a), old(adler_spec_a_u64(bytes, bytes.len(), 1)));
  rewrite(to_integer(state.b), old(adler_spec_b_u64(bytes, bytes.len(), 1, 0)));
  close();
 }
 step();
 have to_integer(statement(4).call(0).result) == 65536 * to_integer(state.b) + to_integer(state.a) by close();
 have to_integer(statement(4).call(0).result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)) by {
  rewrite(to_integer(statement(4).call(0).result), 65536 * to_integer(state.b) + to_integer(state.a));
  close();
 }
 have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by {
  intro() {
   intro() {
    have k < old(bytes.len()) by close();
    have bytes == old(bytes) by close();
    have bytes + k == old(bytes) + k by { rewrite(bytes, old(bytes)); close(); }
    have at(input_bytes, load<uint8>(old(bytes) + k)) == old(bytes[k]) by close();
    have at(region(1).entry, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close();
    have separate(region(1).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(1).exit, load<uint8>(old(bytes) + k)) == at(region(1).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(1)); }
    have at(region(1).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(1).exit, load<uint8>(old(bytes) + k)) == at(region(1).entry, load<uint8>(old(bytes) + k));
     at(region(1).entry, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
     at(input_bytes, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(2).entry, load<uint8>(old(bytes) + k)) == at(region(1).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(2).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(2).exit, load<uint8>(old(bytes) + k)) == at(region(2).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(2)); }
    have at(region(2).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(2).exit, load<uint8>(old(bytes) + k)) == at(region(2).entry, load<uint8>(old(bytes) + k));
     at(region(2).entry, load<uint8>(old(bytes) + k)) == at(region(1).exit, load<uint8>(old(bytes) + k));
     at(region(1).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(3).entry, load<uint8>(old(bytes) + k)) == at(region(2).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(3).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(3).exit, load<uint8>(old(bytes) + k)) == at(region(3).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(3)); }
    have at(region(3).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(3).exit, load<uint8>(old(bytes) + k)) == at(region(3).entry, load<uint8>(old(bytes) + k));
     at(region(3).entry, load<uint8>(old(bytes) + k)) == at(region(2).exit, load<uint8>(old(bytes) + k));
     at(region(2).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(4).entry, load<uint8>(old(bytes) + k)) == at(region(3).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(4).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(4).exit, load<uint8>(old(bytes) + k)) == at(region(4).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(4)); }
    have at(region(4).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(4).exit, load<uint8>(old(bytes) + k)) == at(region(4).entry, load<uint8>(old(bytes) + k));
     at(region(4).entry, load<uint8>(old(bytes) + k)) == at(region(3).exit, load<uint8>(old(bytes) + k));
     at(region(3).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(21).entry, load<uint8>(old(bytes) + k)) == at(region(4).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(21).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(21).exit, load<uint8>(old(bytes) + k)) == at(region(21).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(21)); }
    have at(region(21).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(21).exit, load<uint8>(old(bytes) + k)) == at(region(21).entry, load<uint8>(old(bytes) + k));
     at(region(21).entry, load<uint8>(old(bytes) + k)) == at(region(4).exit, load<uint8>(old(bytes) + k));
     at(region(4).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(24).entry, load<uint8>(old(bytes) + k)) == at(region(21).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(24).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(24).exit, load<uint8>(old(bytes) + k)) == at(region(24).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(24)); }
    have at(region(24).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(24).exit, load<uint8>(old(bytes) + k)) == at(region(24).entry, load<uint8>(old(bytes) + k));
     at(region(24).entry, load<uint8>(old(bytes) + k)) == at(region(21).exit, load<uint8>(old(bytes) + k));
     at(region(21).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(35).entry, load<uint8>(old(bytes) + k)) == at(region(24).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(35).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(35).exit, load<uint8>(old(bytes) + k)) == at(region(35).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(35)); }
    have at(region(35).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(35).exit, load<uint8>(old(bytes) + k)) == at(region(35).entry, load<uint8>(old(bytes) + k));
     at(region(35).entry, load<uint8>(old(bytes) + k)) == at(region(24).exit, load<uint8>(old(bytes) + k));
     at(region(24).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    have at(region(45).entry, load<uint8>(old(bytes) + k)) == at(region(35).exit, load<uint8>(old(bytes) + k)) by close();
    have separate(region(45).footprint, at(input_bytes, memory(bytes[k]))) by close();
    have at(region(45).exit, load<uint8>(old(bytes) + k)) == at(region(45).entry, load<uint8>(old(bytes) + k)) by { preserve(at(input_bytes, memory(bytes[k])), region(45)); }
    have at(region(45).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k)) by close() using {
     at(region(45).exit, load<uint8>(old(bytes) + k)) == at(region(45).entry, load<uint8>(old(bytes) + k));
     at(region(45).entry, load<uint8>(old(bytes) + k)) == at(region(35).exit, load<uint8>(old(bytes) + k));
     at(region(35).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
    };
    rewrite(bytes + k, old(bytes) + k);
    have load<uint8>(old(bytes) + k) == at(region(45).exit, load<uint8>(old(bytes) + k)) by close();
    close() using {
     load<uint8>(old(bytes) + k) == at(region(45).exit, load<uint8>(old(bytes) + k));
     at(region(45).exit, load<uint8>(old(bytes) + k)) == at(input_bytes, load<uint8>(old(bytes) + k));
     at(input_bytes, load<uint8>(old(bytes) + k)) == old(bytes[k]);
    };
   }
  }
 }
 step_until(function.exit);
 close() using { forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) }; };
 close() using { to_integer(statement(4).call(0).result) == old(adler_spec_checksum_u64(bytes, bytes.len(), 1, 0)); };
}
