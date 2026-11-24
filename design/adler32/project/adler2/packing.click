import click::integer;

// The original checksum method packs two u16 fields into a u32.
theorem adler_u16_observation(value: uint16) {
 ensures to_integer(value as uint32) == to_integer(value) by {
  have value as uint32 <= 65535u32;
  have 0 <= to_integer((value as uint32));
  // The promoted word and the narrow field retain the same checked carrier.
  // Prove its range as a word before observing it as a narrow field.
  have to_integer(value) == to_integer(value as uint32) by {
  close() using { 0 <= to_integer(value as uint32); to_integer(value as uint32) <= 65535; };
  }
  rewrite(to_integer(value), to_integer(value as uint32));
  normalize();
 }
}

theorem adler_pack_fields(a: uint16, b: uint16) {
 ensures to_integer((b as uint32 << 16) | a as uint32) == 65536 * to_integer(b) + to_integer(a) by {
  have a as uint32 <= 65535u32;
  have b as uint32 <= 65535u32;
  apply(integer::uint32_pack_uint16_high_first_to_integer(a as uint32, b as uint32));
  apply(adler_u16_observation(a));
  apply(adler_u16_observation(b));
  close() using {
   to_integer((b as uint32 << 16) | a as uint32) == to_integer(a as uint32) + 65536 * to_integer(b as uint32);
   to_integer(a as uint32) == to_integer(a);
   to_integer(b as uint32) == to_integer(b);
  };
 }
}

// Any implementation whose fields meet the shared specification returns its
// specified checksum through the unchanged native packing expression.
theorem adler_pack_fields_spec(a: uint16, b: uint16, bytes: uint8[], length: int32, a0: Integer, b0: Integer) {
 requires 0 <= length;
 requires to_integer(a) == adler_spec_a(bytes, length, a0);
 requires to_integer(b) == adler_spec_b(bytes, length, a0, b0);
 ensures to_integer((b as uint32 << 16) | a as uint32) == adler_spec_checksum(bytes, length, a0, b0) by {
  apply(adler_pack_fields(a, b));
  unfold(adler_spec_checksum(bytes, length, a0, b0));
  close() using {
   to_integer((b as uint32 << 16) | a as uint32) == 65536 * to_integer(b) + to_integer(a);
   to_integer(a) == adler_spec_a(bytes, length, a0);
   to_integer(b) == adler_spec_b(bytes, length, a0, b0);
  };
 }
}

// Canonical observations are accepted unchanged as the next native seed.
theorem adler_canonical_observation(value: uint16) {
 requires to_integer(value) <= 65520;
 ensures value as uint32 <= 65520u32 by {
  apply(adler_u16_observation(value));
  have to_integer(value as uint32) <= to_integer(65520u32) by { rewrite(to_integer(value as uint32), to_integer(value)); known(); }
  known();
 }
}
