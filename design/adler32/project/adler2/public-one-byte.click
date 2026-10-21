// Single-byte public API fragment; the harness adds public-constructors.click.
impl adler2::Adler32 {
    fn write_slice(&mut self, bytes: &[u8]) {
     requires bytes.len() == 1u64;
     requires self.a == 1;
     requires self.b == 0;
     owns self.a;
     owns self.b;
     views bytes[0..1];
     ensures to_integer(self.a) == old(adler_spec_a_u64(bytes, 1u64, 1));
     ensures to_integer(self.b) == old(adler_spec_b_u64(bytes, 1u64, 1, 0));
     ensures bytes[0] == old(bytes[0]);
    } by {
     // The computation states the int32 specification at the constant
     // length; the bridge equates it with the uint64 one.
     have to_integer(1) == to_integer(1u64) by normalize();
     apply(adler_spec_a_bridge(bytes, 1, 1u64, 1)) using { to_integer(1) == to_integer(1u64); };
     apply(adler_spec_b_bridge(bytes, 1, 1u64, 1, 0)) using { to_integer(1) == to_integer(1u64); };
     execute(); simp();
    }
}

fn adler2::adler32_slice(data: &[u8]) -> u32 {
 requires data.len() == 1u64;
 views data[0..1];
 ensures to_integer(result) == old(adler_spec_checksum_u64(data, 1u64, 1, 0));
 ensures data[0] == old(data[0]);
} by {
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a_u64(data, 1u64, 1));
 have to_integer(h.b) == old(adler_spec_b_u64(data, 1u64, 1, 0));
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum_u64(data, 1u64, 1, 0)) by {
  unfold(adler_spec_checksum_u64(data, 1u64, 1, 0));
  rewrite(to_integer(h.a) == old(adler_spec_a_u64(data, 1u64, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b_u64(data, 1u64, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
 have to_integer(__rust_mir_0) == old(adler_spec_checksum_u64(data, 1u64, 1, 0)) by arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum_u64(data, 1u64, 1, 0));
  };
 execute();
 simp();
}
