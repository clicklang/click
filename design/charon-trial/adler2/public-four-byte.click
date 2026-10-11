# Four-byte public API fragment; the harness checks all original callees.
void __rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I11_write_slice(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len == 4u64;
 requires self->a == 1;
 requires self->b == 0;
 owns self->a;
 owns self->b;
 views bytes[0..4];
 ensures to_integer(self->a) == old(adler_spec_a(bytes, 4, 1));
 ensures to_integer(self->b) == old(adler_spec_b(bytes, 4, 1, 0));
 ensures bytes[0] == old(bytes[0]);
 ensures bytes[1] == old(bytes[1]);
 ensures bytes[2] == old(bytes[2]);
 ensures bytes[3] == old(bytes[3]);
} by { execute(); simp(); }

uint32 __rust_q_I6_adler2_I13_adler32_slice(const uint8* data, uint64 data_len) {
 requires data_len == 4u64;
 views data[0..4];
 ensures to_integer(result) == old(adler_spec_checksum(data, 4, 1, 0));
 ensures data[0] == old(data[0]);
 ensures data[1] == old(data[1]);
 ensures data[2] == old(data[2]);
 ensures data[3] == old(data[3]);
} by {
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a(data, 4, 1)) by { simp(); }
 have to_integer(h.b) == old(adler_spec_b(data, 4, 1, 0)) by { simp(); }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 4, 1, 0)) by {
  unfold(adler_spec_checksum(data, 4, 1, 0));
  rewrite(to_integer(h.a) == old(adler_spec_a(data, 4, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, 4, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a) by { simp(); }
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, 4, 1, 0)) by {
  arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 4, 1, 0));
  }
 }
 execute();
 simp();
}
