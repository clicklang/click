// General public API composition; the harness checks all unchanged callee bodies.
impl adler2::Adler32 {
    fn write_slice(&mut self, bytes: &[u8]) {
     requires (self.a as u32) <= 65520u32;
     requires (self.b as u32) <= 65520u32;
     owns self.a;
     owns self.b;
     views *bytes;
     ensures to_integer(self.a) == old(adler_spec_a_u64(bytes, bytes.len(), old(to_integer((self.a as u32)))));
     ensures to_integer(self.b) == old(adler_spec_b_u64(bytes, bytes.len(), old(to_integer((self.a as u32))), old(to_integer((self.b as u32)))));
     ensures self.a < 65521;
     ensures self.b < 65521;
     ensures (self.a as u32) <= 65520u32;
     ensures (self.b as u32) <= 65520u32;
     ensures forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) };
    } by {
     // The computation states the uint64 specification at the slice's own length.
     step_until(function.exit);
     apply(adler_canonical_observation(self.a));
     apply(adler_canonical_observation(self.b));
     have forall (k: uint64) { k < bytes.len() implies bytes[k] == old(bytes[k]) } by close();
     close();
    }
}

fn adler2::adler32_slice(data: &[u8]) -> u32 {
 views *data;
 ensures forall (k: uint64) { k < data.len() implies data[k] == old(data[k]) };
 ensures to_integer(result) == old(adler_spec_checksum_u64(data, data.len(), 1, 0));
} by {
 step_until(statement(1).call(0).entry);
 have h.a == 1 by close();
 have h.b == 0 by close();
 have to_integer((h.a as u32)) == 1 by { rewrite(h.a, 1); normalize(); }
 have to_integer((h.b as u32)) == 0 by { rewrite(h.b, 0); normalize(); }
 mark canonical_seed;
 step_until(statement(2).call(0).entry);
 have forall (k: uint64) { k < data.len() implies data[k] == old(data[k]) } by close();
 have to_integer(h.a) == old(adler_spec_a_u64(data, data.len(), 1)) by {
  rewrite(1, at(canonical_seed, to_integer((h.a as u32))));
  close();
 }
 have to_integer(h.b) == old(adler_spec_b_u64(data, data.len(), 1, 0)) by {
  rewrite(1, at(canonical_seed, to_integer((h.a as u32))));
  rewrite(0, at(canonical_seed, to_integer((h.b as u32))));
  close();
 }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum_u64(data, data.len(), 1, 0)) by {
  unfold(adler_spec_checksum_u64(data, data.len(), 1, 0));
  rewrite(to_integer(h.a), old(adler_spec_a_u64(data, data.len(), 1)));
  rewrite(to_integer(h.b), old(adler_spec_b_u64(data, data.len(), 1, 0)));
  close();
 }
 step();
 have to_integer(statement(2).call(0).result) == 65536 * to_integer(h.b) + to_integer(h.a);
 have to_integer(statement(2).call(0).result) == old(adler_spec_checksum_u64(data, data.len(), 1, 0)) by close() using {
   to_integer(statement(2).call(0).result) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum_u64(data, data.len(), 1, 0));
  };
}
