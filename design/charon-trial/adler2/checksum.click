# Contract fragment for the unchanged shared checksum getter.
# The harness combines this with packing.click and the locked crate import.
uint32 __rust_q_I6_adler2_T29___rust_q_I6_adler2_I7_Adler32_I8_checksum(const struct __rust_q_I6_adler2_I7_Adler32* self) {
 views self->a;
 views self->b;
 ensures to_integer(result) == 65536 * old(to_integer(self->b)) + old(to_integer(self->a));
 ensures self->a == old(self->a);
 ensures self->b == old(self->b);
} by {
 apply(adler_pack_fields(self->a, self->b));
 execute();
 have result == old(((uint32)self->b << 16) | (uint32)self->a) by { simp(); }
 rewrite(result == old(((uint32)self->b << 16) | (uint32)self->a));
 simp();
}
