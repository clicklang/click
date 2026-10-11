# Two-byte public API fragment; the harness adds public-constructors.click.
void __rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I11_write_slice(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len == 2u64;
 requires self->a == 1;
 requires self->b == 0;
 owns self->a;
 owns self->b;
 views bytes[0..2];
 ensures to_integer(self->a) == old(adler_spec_a(bytes, 2, 1));
 ensures to_integer(self->b) == old(adler_spec_b(bytes, 2, 1, 0));
 ensures bytes[0] == old(bytes[0]);
 ensures bytes[1] == old(bytes[1]);
} by { execute(); simp(); }

uint32 __rust_q_I6_adler2_I13_adler32_slice(const uint8* data, uint64 data_len) {
 requires data_len == 2u64;
 views data[0..2];
 ensures to_integer(result) == old(adler_spec_checksum(data, 2, 1, 0));
 ensures data[0] == old(data[0]);
 ensures data[1] == old(data[1]);
} by {
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a(data, 2, 1)) by { simp(); }
 have to_integer(h.b) == old(adler_spec_b(data, 2, 1, 0)) by { simp(); }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 2, 1, 0)) by {
  unfold(adler_spec_checksum(data, 2, 1, 0));
  rewrite(to_integer(h.a) == old(adler_spec_a(data, 2, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, 2, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a) by { simp(); }
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, 2, 1, 0)) by {
  arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 2, 1, 0));
  }
 }
 execute();
 simp();
}
