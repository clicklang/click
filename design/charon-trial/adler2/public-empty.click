# Empty public API fragment; no input-byte authority or dereference is needed.
void __rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I11_write_slice(struct __rust_q_I6_adler2_I7_Adler32* self, const uint8* bytes, uint64 bytes_len) {
 requires bytes_len == 0u64;
 requires self->a == 1;
 requires self->b == 0;
 owns self->a;
 owns self->b;
 views bytes[0..0];
 ensures self->a == 1;
 ensures self->b == 0;
} by { execute(); simp(); }

uint32 __rust_q_I6_adler2_I13_adler32_slice(const uint8* data, uint64 data_len) {
 requires data_len == 0u64;
 views data[0..0];
 ensures to_integer(result) == old(adler_spec_checksum(data, 0, 1, 0));
} by {
 apply(adler_spec_empty(data, 1, 0));
 unfold(adler_spec_checksum(data, 0, 1, 0));
 execute_until(assignment(__rust_mir_0, 0));
 have to_integer(h.a) == old(adler_spec_a(data, 0, 1)) by {
  rewrite(old(adler_spec_a(data, 0, 1)) == 1);
  rewrite(h.a == 1);
  simp();
 }
 have to_integer(h.b) == old(adler_spec_b(data, 0, 1, 0)) by {
  rewrite(old(adler_spec_b(data, 0, 1, 0)) == 0);
  rewrite(h.b == 0);
  simp();
 }
 have 65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 0, 1, 0)) by {
  rewrite(to_integer(h.a) == old(adler_spec_a(data, 0, 1)));
  rewrite(to_integer(h.b) == old(adler_spec_b(data, 0, 1, 0)));
  simp();
 }
 step();
 have to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a) by { simp(); }
 have to_integer(__rust_mir_0) == old(adler_spec_checksum(data, 0, 1, 0)) by {
  arithmetic() using {
   to_integer(__rust_mir_0) == 65536 * to_integer(h.b) + to_integer(h.a);
   65536 * to_integer(h.b) + to_integer(h.a) == old(adler_spec_checksum(data, 0, 1, 0));
  }
 }
 execute();
 simp();
}
