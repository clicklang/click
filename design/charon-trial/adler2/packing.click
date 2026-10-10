# The original checksum method packs two u16 fields into a u32.
theorem adler_u16_observation(value: uint16) {
 ensures to_integer((uint32)value) == to_integer(value) by {
  have (uint32)value <= 65535u32 by { simp(); }
  apply(uint32_to_integer_bounds((uint32)value));
  apply(uint32_less_equal_to_integer((uint32)value, 65535u32));
  # The promoted word and the narrow field retain the same checked carrier.
  # Prove its range as a word before observing it as a narrow field.
  have to_integer(value) == to_integer((uint32)value) by {
  arithmetic_certificate special {
   premise 0: 0 <= to_integer((uint32)value) => 0 <= to_integer((uint32)value);
   premise 1: to_integer((uint32)value) <= 65535 => to_integer((uint32)value) <= 65535;
   integer_cast_identity bounds [0, 1] => to_integer(value) == to_integer((uint32)value);
   conclusion 0;
  }
  }
  rewrite(to_integer(value) == to_integer((uint32)value));
  normalize();
 }
}

theorem adler_pack_fields(a: uint16, b: uint16) {
 ensures to_integer(((uint32)b << 16) | (uint32)a) == 65536 * to_integer(b) + to_integer(a) by {
  have (uint32)a <= 65535u32 by { simp(); }
  have (uint32)b <= 65535u32 by { simp(); }
  apply(uint32_pack_u16_high_first_to_integer((uint32)a, (uint32)b));
  apply(adler_u16_observation(a));
  apply(adler_u16_observation(b));
  arithmetic() using {
   to_integer(((uint32)b << 16) | (uint32)a) == to_integer((uint32)a) + 65536 * to_integer((uint32)b);
   to_integer((uint32)a) == to_integer(a);
   to_integer((uint32)b) == to_integer(b);
  }
 }
}

# Any implementation whose fields meet the shared specification returns its
# specified checksum through the unchanged native packing expression.
theorem adler_pack_fields_spec(a: uint16, b: uint16, bytes: uint8[], length: int32, a0: Integer, b0: Integer) {
 requires 0 <= length;
 requires to_integer(a) == adler_spec_a(bytes, length, a0);
 requires to_integer(b) == adler_spec_b(bytes, length, a0, b0);
 ensures to_integer(((uint32)b << 16) | (uint32)a) == adler_spec_checksum(bytes, length, a0, b0) by {
  apply(adler_pack_fields(a, b));
  unfold(adler_spec_checksum(bytes, length, a0, b0));
  arithmetic() using {
   to_integer(((uint32)b << 16) | (uint32)a) == 65536 * to_integer(b) + to_integer(a);
   to_integer(a) == adler_spec_a(bytes, length, a0);
   to_integer(b) == adler_spec_b(bytes, length, a0, b0);
  }
 }
}
