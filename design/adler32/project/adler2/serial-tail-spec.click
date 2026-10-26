import click::integer;

// Checked native serial-tail sums and their connection to the common spec.
theorem adler_serial_byte_observation(value: uint8) {
 ensures to_integer(value as uint32) == to_integer(value as int32)
     and 0 <= to_integer(value as uint32) and to_integer(value as uint32) <= 255 by {
  apply(adler_byte_bounds(value));
  have to_integer(value as uint32) == to_integer(value as int32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32) == to_integer(value as int32);
   conclusion 0;
  } }
  have 0 <= to_integer(value as uint32) by {
   rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption();
  }
  have to_integer(value as uint32) <= 255 by {
   rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption();
  }
  solve();
 }
}

theorem adler_serial_two_native_result(x0: uint8, x1: uint8) {
 ensures to_integer(((1u32 + x0 as uint32) + x1 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32), 65521)
     and to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) % 65521u32) == truncating_remainder(2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 65521) by {
  apply(adler_serial_byte_observation(x0));
  apply(adler_byte_bounds(x0));
  apply(adler_serial_byte_observation(x1));
  apply(adler_byte_bounds(x1));
  have to_integer(1u32) + to_integer(x0 as uint32) <= 4294967295 by solve() using { to_integer(x0 as uint32) <= 255; };
  have to_integer(1u32 + (x0 as uint32)) == to_integer(1u32) + to_integer((x0 as uint32));
  have to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32) by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); to_integer(x0 as uint32) == to_integer(x0 as int32); };
  have to_integer((1u32 + x0 as uint32)) <= 256 by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
  have to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32) <= 4294967295 by solve() using { to_integer((1u32 + x0 as uint32)) <= 256; to_integer(x1 as uint32) <= 255; };
  have to_integer(((1u32 + x0 as uint32)) + (x1 as uint32)) == to_integer(((1u32 + x0 as uint32))) + to_integer((x1 as uint32));
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32); to_integer(x1 as uint32) == to_integer(x1 as int32); };
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511 by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); to_integer((1u32 + x0 as uint32)) <= 256; to_integer(x1 as uint32) <= 255; };
  have to_integer(393126u32) + to_integer((1u32 + x0 as uint32)) <= 4294967295 by solve() using { to_integer((1u32 + x0 as uint32)) <= 256; };
  have to_integer(393126u32 + ((1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer(((1u32 + x0 as uint32)));
  have to_integer((393126u32 + (1u32 + x0 as uint32))) == 393126 + 1 + to_integer(x0 as int32) by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32); };
  have to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382 by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) <= 256; };
  have to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 4294967295 by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382; to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; };
  have to_integer(((393126u32 + (1u32 + x0 as uint32))) + (((1u32 + x0 as uint32) + x1 as uint32))) == to_integer(((393126u32 + (1u32 + x0 as uint32)))) + to_integer((((1u32 + x0 as uint32) + x1 as uint32)));
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32) by solve() using { to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer((393126u32 + (1u32 + x0 as uint32))) == 393126 + 1 + to_integer(x0 as int32); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32); };
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) <= 393893 by solve() using { to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382; to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; };
  apply(integer::uint32_remainder_to_integer(((1u32 + x0 as uint32) + x1 as uint32), 65521u32));
  apply(integer::uint32_remainder_to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)), 65521u32));
  have 0 <= 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32) by { arithmetic_certificate {
   premise 0: 0 <= to_integer(x0 as int32) => 0 <= to_integer(x0 as int32);
   scale 0 by 2 => 0 <= 2 * to_integer(x0 as int32);
   premise 1: 0 <= to_integer(x1 as int32) => 0 <= to_integer(x1 as int32);
   trivial => 0 <= 2;
   add 3, 1 => 0 <= 2 + 2 * to_integer(x0 as int32);
   add 4, 2 => 0 <= 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32);
   conclusion 5;
  } }
  have 0 <= 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32) by solve() using { 0 <= 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32); };
  have 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32) == (2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32)) + 65521 * 6 by solve() using {};
  apply(adler_residue_congruent(393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 6));
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32), 65521) by {
   rewrite(to_integer(((1u32 + x0 as uint32) + x1 as uint32) % 65521u32) == truncating_remainder(to_integer(((1u32 + x0 as uint32) + x1 as uint32)), to_integer(65521u32)));
   rewrite(to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32));
   normalize();
  }
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) % 65521u32) == truncating_remainder(2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 65521) by {
   rewrite(to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) % 65521u32) == truncating_remainder(to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))), to_integer(65521u32)));
   rewrite(to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32));
   rewrite(truncating_remainder(393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 65521) == truncating_remainder(2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32), 65521));
   normalize();
  }
  solve();
 }
}

theorem adler_serial_two_result_spec(bytes: uint8[]) {
 ensures to_integer(((1u32 + bytes[0] as uint32) + bytes[1] as uint32) % 65521u32) == adler_spec_a(bytes, 2, 1) by {
  apply(adler_spec_two(bytes));
  apply(adler_serial_two_native_result(bytes[0], bytes[1]));
  rewrite(adler_spec_a(bytes, 2, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32), 65521));
  assumption();
 }
 ensures to_integer(((393126u32 + (1u32 + bytes[0] as uint32)) + ((1u32 + bytes[0] as uint32) + bytes[1] as uint32)) % 65521u32) == adler_spec_b(bytes, 2, 1, 0) by {
  apply(adler_spec_two(bytes));
  apply(adler_serial_two_native_result(bytes[0], bytes[1]));
  rewrite(adler_spec_b(bytes, 2, 1, 0) == truncating_remainder(2 + 2 * to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32), 65521));
  assumption();
 }
}

theorem adler_serial_three_native_result(x0: uint8, x1: uint8, x2: uint8) {
 ensures to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32), 65521)
     and to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) % 65521u32) == truncating_remainder(3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 65521) by {
  apply(adler_serial_byte_observation(x0));
  apply(adler_byte_bounds(x0));
  apply(adler_serial_byte_observation(x1));
  apply(adler_byte_bounds(x1));
  apply(adler_serial_byte_observation(x2));
  apply(adler_byte_bounds(x2));
  have to_integer(1u32) + to_integer(x0 as uint32) <= 4294967295 by solve() using { to_integer(x0 as uint32) <= 255; };
  have to_integer(1u32 + (x0 as uint32)) == to_integer(1u32) + to_integer((x0 as uint32));
  have to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32) by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); to_integer(x0 as uint32) == to_integer(x0 as int32); };
  have to_integer((1u32 + x0 as uint32)) <= 256 by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
  have to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32) <= 4294967295 by solve() using { to_integer((1u32 + x0 as uint32)) <= 256; to_integer(x1 as uint32) <= 255; };
  have to_integer(((1u32 + x0 as uint32)) + (x1 as uint32)) == to_integer(((1u32 + x0 as uint32))) + to_integer((x1 as uint32));
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32); to_integer(x1 as uint32) == to_integer(x1 as int32); };
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511 by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); to_integer((1u32 + x0 as uint32)) <= 256; to_integer(x1 as uint32) <= 255; };
  have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32) <= 4294967295 by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; to_integer(x2 as uint32) <= 255; };
  have to_integer((((1u32 + x0 as uint32) + x1 as uint32)) + (x2 as uint32)) == to_integer((((1u32 + x0 as uint32) + x1 as uint32))) + to_integer((x2 as uint32));
  have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32) by solve() using { to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32); to_integer(x2 as uint32) == to_integer(x2 as int32); };
  have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766 by solve() using { to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; to_integer(x2 as uint32) <= 255; };
  have to_integer(393126u32) + to_integer((1u32 + x0 as uint32)) <= 4294967295 by solve() using { to_integer((1u32 + x0 as uint32)) <= 256; };
  have to_integer(393126u32 + ((1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer(((1u32 + x0 as uint32)));
  have to_integer((393126u32 + (1u32 + x0 as uint32))) == 393126 + 1 + to_integer(x0 as int32) by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) == 1 + to_integer(x0 as int32); };
  have to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382 by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) == to_integer(393126u32) + to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) <= 256; };
  have to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 4294967295 by solve() using { to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382; to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; };
  have to_integer(((393126u32 + (1u32 + x0 as uint32))) + (((1u32 + x0 as uint32) + x1 as uint32))) == to_integer(((393126u32 + (1u32 + x0 as uint32)))) + to_integer((((1u32 + x0 as uint32) + x1 as uint32)));
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32) by solve() using { to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer((393126u32 + (1u32 + x0 as uint32))) == 393126 + 1 + to_integer(x0 as int32); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32); };
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) <= 393893 by solve() using { to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == to_integer((393126u32 + (1u32 + x0 as uint32))) + to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer((393126u32 + (1u32 + x0 as uint32))) <= 393382; to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; };
  have to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) + to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 4294967295 by solve() using { to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) <= 393893; to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766; };
  have to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) + ((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) == to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)))) + to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)));
  have to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) == 393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32) by {
   rewrite(to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) == to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) + to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)));
   rewrite(to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) == 393126 + 2 + 2 * to_integer(x0 as int32) + to_integer(x1 as int32));
   rewrite(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32));
   solve() using {};
  }
  have to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) <= 394659 by solve() using { to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) == to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) + to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)); to_integer(((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32))) <= 393893; to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766; };
  apply(integer::uint32_remainder_to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32), 65521u32));
  apply(integer::uint32_remainder_to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)), 65521u32));
  have 0 <= 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32) by { arithmetic_certificate {
   premise 0: 0 <= to_integer(x0 as int32) => 0 <= to_integer(x0 as int32);
   scale 0 by 3 => 0 <= 3 * to_integer(x0 as int32);
   premise 1: 0 <= to_integer(x1 as int32) => 0 <= to_integer(x1 as int32);
   scale 2 by 2 => 0 <= 2 * to_integer(x1 as int32);
   premise 2: 0 <= to_integer(x2 as int32) => 0 <= to_integer(x2 as int32);
   trivial => 0 <= 3;
   add 5, 1 => 0 <= 3 + 3 * to_integer(x0 as int32);
   add 6, 3 => 0 <= 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32);
   add 7, 4 => 0 <= 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32);
   conclusion 8;
  } }
  have 0 <= 393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32) by solve() using { 0 <= 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32); };
  have 393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32) == (3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32)) + 65521 * 6 by solve() using {};
  apply(adler_residue_congruent(393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 6));
  have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32), 65521) by {
   rewrite(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) % 65521u32) == truncating_remainder(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)), to_integer(65521u32)));
   rewrite(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32));
   normalize();
  }
  have to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) % 65521u32) == truncating_remainder(3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 65521) by {
   rewrite(to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) % 65521u32) == truncating_remainder(to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))), to_integer(65521u32)));
   rewrite(to_integer((((393126u32 + (1u32 + x0 as uint32)) + ((1u32 + x0 as uint32) + x1 as uint32)) + (((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) == 393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32));
   rewrite(truncating_remainder(393126 + 3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 65521) == truncating_remainder(3 + 3 * to_integer(x0 as int32) + 2 * to_integer(x1 as int32) + to_integer(x2 as int32), 65521));
   normalize();
  }
  solve();
 }
}

theorem adler_serial_three_result_spec(bytes: uint8[]) {
 ensures to_integer((((1u32 + bytes[0] as uint32) + bytes[1] as uint32) + bytes[2] as uint32) % 65521u32) == adler_spec_a(bytes, 3, 1) by {
  apply(adler_spec_three(bytes));
  apply(adler_serial_three_native_result(bytes[0], bytes[1], bytes[2]));
  rewrite(adler_spec_a(bytes, 3, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32), 65521));
  assumption();
 }
 ensures to_integer((((393126u32 + (1u32 + bytes[0] as uint32)) + ((1u32 + bytes[0] as uint32) + bytes[1] as uint32)) + (((1u32 + bytes[0] as uint32) + bytes[1] as uint32) + bytes[2] as uint32)) % 65521u32) == adler_spec_b(bytes, 3, 1, 0) by {
  apply(adler_spec_three(bytes));
  apply(adler_serial_three_native_result(bytes[0], bytes[1], bytes[2]));
  rewrite(adler_spec_b(bytes, 3, 1, 0) == truncating_remainder(3 + 3 * to_integer(bytes[0] as int32) + 2 * to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32), 65521));
  assumption();
 }
}
