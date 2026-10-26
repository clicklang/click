import click::integer;

// Checked bridge from the original four-byte recombination to the common spec.
// Assemble after design/adler32/project/adler32-spec.click. No computation summary is assumed.

theorem adler_four_byte_native_result(x0: uint8, x1: uint8, x2: uint8, x3: uint8) {
 ensures to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32) + to_integer(x3 as int32), 65521)
     and to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) % 65521u32) == truncating_remainder(4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32), 65521) by {
 apply(adler_byte_bounds(x0));
 have to_integer(x0 as uint32) == to_integer(x0 as int32) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer(x0 as int32) => 0 <= to_integer(x0 as int32);
  premise 1: to_integer(x0 as int32) <= 255 => to_integer(x0 as int32) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer(x0 as uint32) == to_integer(x0 as int32); conclusion 0;
 } }
 have 0 <= to_integer(x0 as uint32) by solve() using { to_integer(x0 as uint32) == to_integer(x0 as int32); 0 <= to_integer(x0 as int32); to_integer(x0 as int32) <= 255; };
 have to_integer(x0 as uint32) <= 255 by solve() using { to_integer(x0 as uint32) == to_integer(x0 as int32); 0 <= to_integer(x0 as int32); to_integer(x0 as int32) <= 255; };
 apply(adler_byte_bounds(x1));
 have to_integer(x1 as uint32) == to_integer(x1 as int32) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer(x1 as int32) => 0 <= to_integer(x1 as int32);
  premise 1: to_integer(x1 as int32) <= 255 => to_integer(x1 as int32) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer(x1 as uint32) == to_integer(x1 as int32); conclusion 0;
 } }
 have 0 <= to_integer(x1 as uint32) by solve() using { to_integer(x1 as uint32) == to_integer(x1 as int32); 0 <= to_integer(x1 as int32); to_integer(x1 as int32) <= 255; };
 have to_integer(x1 as uint32) <= 255 by solve() using { to_integer(x1 as uint32) == to_integer(x1 as int32); 0 <= to_integer(x1 as int32); to_integer(x1 as int32) <= 255; };
 apply(adler_byte_bounds(x2));
 have to_integer(x2 as uint32) == to_integer(x2 as int32) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer(x2 as int32) => 0 <= to_integer(x2 as int32);
  premise 1: to_integer(x2 as int32) <= 255 => to_integer(x2 as int32) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer(x2 as uint32) == to_integer(x2 as int32); conclusion 0;
 } }
 have 0 <= to_integer(x2 as uint32) by solve() using { to_integer(x2 as uint32) == to_integer(x2 as int32); 0 <= to_integer(x2 as int32); to_integer(x2 as int32) <= 255; };
 have to_integer(x2 as uint32) <= 255 by solve() using { to_integer(x2 as uint32) == to_integer(x2 as int32); 0 <= to_integer(x2 as int32); to_integer(x2 as int32) <= 255; };
 apply(adler_byte_bounds(x3));
 have to_integer(x3 as uint32) == to_integer(x3 as int32) by { arithmetic_certificate rules {
  premise 0: 0 <= to_integer(x3 as int32) => 0 <= to_integer(x3 as int32);
  premise 1: to_integer(x3 as int32) <= 255 => to_integer(x3 as int32) <= 255;
  integer_cast_identity bounds [0, 1] => to_integer(x3 as uint32) == to_integer(x3 as int32); conclusion 0;
 } }
 have 0 <= to_integer(x3 as uint32) by solve() using { to_integer(x3 as uint32) == to_integer(x3 as int32); 0 <= to_integer(x3 as int32); to_integer(x3 as int32) <= 255; };
 have to_integer(x3 as uint32) <= 255 by solve() using { to_integer(x3 as uint32) == to_integer(x3 as int32); 0 <= to_integer(x3 as int32); to_integer(x3 as int32) <= 255; };
 have to_integer(1u32) + to_integer(x0 as uint32) <= 4294967295 by solve() using { to_integer(x0 as uint32) <= 255; };
 have to_integer(1u32 + (x0 as uint32)) == to_integer(1u32) + to_integer((x0 as uint32));
 have to_integer((1u32 + x0 as uint32)) == (1 + to_integer(x0 as int32)) by {
  rewrite(to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32));
  rewrite(to_integer(x0 as uint32) == to_integer(x0 as int32));
  normalize();
 }
 have 1 <= to_integer((1u32 + x0 as uint32)) by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); 0 <= to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
 have to_integer((1u32 + x0 as uint32)) <= 256 by solve() using { to_integer((1u32 + x0 as uint32)) == to_integer(1u32) + to_integer(x0 as uint32); 0 <= to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
 have to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32) <= 4294967295 by solve() using { to_integer((1u32 + x0 as uint32)) <= 256; to_integer(x1 as uint32) <= 255; };
 have to_integer(((1u32 + x0 as uint32)) + (x1 as uint32)) == to_integer(((1u32 + x0 as uint32))) + to_integer((x1 as uint32));
 have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == ((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)) by {
  rewrite(to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32));
  rewrite(to_integer((1u32 + x0 as uint32)) == (1 + to_integer(x0 as int32)));
  rewrite(to_integer(x1 as uint32) == to_integer(x1 as int32));
  normalize();
 }
 have 1 <= to_integer(((1u32 + x0 as uint32) + x1 as uint32)) by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); 1 <= to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) <= 256; 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511 by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == to_integer((1u32 + x0 as uint32)) + to_integer(x1 as uint32); 1 <= to_integer((1u32 + x0 as uint32)); to_integer((1u32 + x0 as uint32)) <= 256; 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32) <= 4294967295 by solve() using { to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; to_integer(x2 as uint32) <= 255; };
 have to_integer((((1u32 + x0 as uint32) + x1 as uint32)) + (x2 as uint32)) == to_integer((((1u32 + x0 as uint32) + x1 as uint32))) + to_integer((x2 as uint32));
 have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == (((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)) + to_integer(x2 as int32)) by {
  rewrite(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32));
  rewrite(to_integer(((1u32 + x0 as uint32) + x1 as uint32)) == ((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)));
  rewrite(to_integer(x2 as uint32) == to_integer(x2 as int32));
  normalize();
 }
 have 1 <= to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) by solve() using { to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32); 1 <= to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766 by solve() using { to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == to_integer(((1u32 + x0 as uint32) + x1 as uint32)) + to_integer(x2 as uint32); 1 <= to_integer(((1u32 + x0 as uint32) + x1 as uint32)); to_integer(((1u32 + x0 as uint32) + x1 as uint32)) <= 511; 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) + to_integer(x3 as uint32) <= 4294967295 by solve() using { to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766; to_integer(x3 as uint32) <= 255; };
 have to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) + (x3 as uint32)) == to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32))) + to_integer((x3 as uint32));
 have to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == ((((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)) + to_integer(x2 as int32)) + to_integer(x3 as int32)) by {
  rewrite(to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) + to_integer(x3 as uint32));
  rewrite(to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) == (((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)) + to_integer(x2 as int32)));
  rewrite(to_integer(x3 as uint32) == to_integer(x3 as int32));
  normalize();
 }
 have 1 <= to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) by solve() using { to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) + to_integer(x3 as uint32); 1 <= to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)); to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766; 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) <= 1021 by solve() using { to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) + to_integer(x3 as uint32); 1 <= to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)); to_integer((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32)) <= 766; 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer(x0 as uint32) <= 1073741823 by solve() using { to_integer(x0 as uint32) <= 255; };
 have x0 as uint32 <= 4294967295u32 / 4u32 by solve() using { x0 as uint32 <= 1073741823u32; };
 have 4u32 == 0u32 or x0 as uint32 <= 4294967295u32 / 4u32 by assumption();
 apply(integer::uint32_multiply_to_integer(x0 as uint32, 4u32)) using { 4u32 == 0u32 or x0 as uint32 <= 4294967295u32 / 4u32; };
 have to_integer((x0 as uint32 * 4u32)) == (to_integer(x0 as int32) * 4) by {
  rewrite(to_integer((x0 as uint32 * 4u32)) == to_integer(x0 as uint32) * to_integer(4u32));
  rewrite(to_integer(x0 as uint32) == to_integer(x0 as int32));
  normalize();
 }
 have 0 <= to_integer((x0 as uint32 * 4u32)) by solve() using { to_integer((x0 as uint32 * 4u32)) == to_integer(x0 as uint32) * to_integer(4u32); 0 <= to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
 have to_integer((x0 as uint32 * 4u32)) <= 1020 by solve() using { to_integer((x0 as uint32 * 4u32)) == to_integer(x0 as uint32) * to_integer(4u32); 0 <= to_integer(x0 as uint32); to_integer(x0 as uint32) <= 255; };
 have to_integer(4u32) + to_integer((x0 as uint32 * 4u32)) <= 4294967295 by solve() using { to_integer((x0 as uint32 * 4u32)) <= 1020; };
 have to_integer(4u32 + ((x0 as uint32 * 4u32))) == to_integer(4u32) + to_integer(((x0 as uint32 * 4u32)));
 have to_integer((4u32 + (x0 as uint32 * 4u32))) == (4 + (to_integer(x0 as int32) * 4)) by {
  rewrite(to_integer((4u32 + (x0 as uint32 * 4u32))) == to_integer(4u32) + to_integer((x0 as uint32 * 4u32)));
  rewrite(to_integer((x0 as uint32 * 4u32)) == (to_integer(x0 as int32) * 4));
  normalize();
 }
 have 4 <= to_integer((4u32 + (x0 as uint32 * 4u32))) by solve() using { to_integer((4u32 + (x0 as uint32 * 4u32))) == to_integer(4u32) + to_integer((x0 as uint32 * 4u32)); 0 <= to_integer((x0 as uint32 * 4u32)); to_integer((x0 as uint32 * 4u32)) <= 1020; };
 have to_integer((4u32 + (x0 as uint32 * 4u32))) <= 1024 by solve() using { to_integer((4u32 + (x0 as uint32 * 4u32))) == to_integer(4u32) + to_integer((x0 as uint32 * 4u32)); 0 <= to_integer((x0 as uint32 * 4u32)); to_integer((x0 as uint32 * 4u32)) <= 1020; };
 have to_integer(x1 as uint32) <= 1073741823 by solve() using { to_integer(x1 as uint32) <= 255; };
 have x1 as uint32 <= 4294967295u32 / 4u32 by solve() using { x1 as uint32 <= 1073741823u32; };
 have 4u32 == 0u32 or x1 as uint32 <= 4294967295u32 / 4u32 by assumption();
 apply(integer::uint32_multiply_to_integer(x1 as uint32, 4u32)) using { 4u32 == 0u32 or x1 as uint32 <= 4294967295u32 / 4u32; };
 have to_integer((x1 as uint32 * 4u32)) == (to_integer(x1 as int32) * 4) by {
  rewrite(to_integer((x1 as uint32 * 4u32)) == to_integer(x1 as uint32) * to_integer(4u32));
  rewrite(to_integer(x1 as uint32) == to_integer(x1 as int32));
  normalize();
 }
 have 0 <= to_integer((x1 as uint32 * 4u32)) by solve() using { to_integer((x1 as uint32 * 4u32)) == to_integer(x1 as uint32) * to_integer(4u32); 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer((x1 as uint32 * 4u32)) <= 1020 by solve() using { to_integer((x1 as uint32 * 4u32)) == to_integer(x1 as uint32) * to_integer(4u32); 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer(x1 as uint32) <= 65521 by solve() using { to_integer(x1 as uint32) <= 255; };
 have to_integer(65521u32 - (x1 as uint32)) == to_integer(65521u32) - to_integer((x1 as uint32));
 have to_integer((65521u32 - x1 as uint32)) == (65521 - to_integer(x1 as int32)) by {
  rewrite(to_integer((65521u32 - x1 as uint32)) == to_integer(65521u32) - to_integer(x1 as uint32));
  rewrite(to_integer(x1 as uint32) == to_integer(x1 as int32));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - x1 as uint32)) by solve() using { to_integer((65521u32 - x1 as uint32)) == to_integer(65521u32) - to_integer(x1 as uint32); 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer((65521u32 - x1 as uint32)) <= 65521 by solve() using { to_integer((65521u32 - x1 as uint32)) == to_integer(65521u32) - to_integer(x1 as uint32); 0 <= to_integer(x1 as uint32); to_integer(x1 as uint32) <= 255; };
 have to_integer((x1 as uint32 * 4u32)) + to_integer((65521u32 - x1 as uint32)) <= 4294967295 by solve() using { to_integer((x1 as uint32 * 4u32)) <= 1020; to_integer((65521u32 - x1 as uint32)) <= 65521; };
 have to_integer(((x1 as uint32 * 4u32)) + ((65521u32 - x1 as uint32))) == to_integer(((x1 as uint32 * 4u32))) + to_integer(((65521u32 - x1 as uint32)));
 have to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) == ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32))) by {
  rewrite(to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) == to_integer((x1 as uint32 * 4u32)) + to_integer((65521u32 - x1 as uint32)));
  rewrite(to_integer((x1 as uint32 * 4u32)) == (to_integer(x1 as int32) * 4));
  rewrite(to_integer((65521u32 - x1 as uint32)) == (65521 - to_integer(x1 as int32)));
  normalize();
 }
 have 65266 <= to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) by solve() using { to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) == to_integer((x1 as uint32 * 4u32)) + to_integer((65521u32 - x1 as uint32)); 0 <= to_integer((x1 as uint32 * 4u32)); to_integer((x1 as uint32 * 4u32)) <= 1020; 65266 <= to_integer((65521u32 - x1 as uint32)); to_integer((65521u32 - x1 as uint32)) <= 65521; };
 have to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) <= 66541 by solve() using { to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) == to_integer((x1 as uint32 * 4u32)) + to_integer((65521u32 - x1 as uint32)); 0 <= to_integer((x1 as uint32 * 4u32)); to_integer((x1 as uint32 * 4u32)) <= 1020; 65266 <= to_integer((65521u32 - x1 as uint32)); to_integer((65521u32 - x1 as uint32)) <= 65521; };
 have to_integer((4u32 + (x0 as uint32 * 4u32))) + to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) <= 4294967295 by solve() using { to_integer((4u32 + (x0 as uint32 * 4u32))) <= 1024; to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) <= 66541; };
 have to_integer(((4u32 + (x0 as uint32 * 4u32))) + (((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == to_integer(((4u32 + (x0 as uint32 * 4u32)))) + to_integer((((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))));
 have to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == ((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))) by {
  rewrite(to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == to_integer((4u32 + (x0 as uint32 * 4u32))) + to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))));
  rewrite(to_integer((4u32 + (x0 as uint32 * 4u32))) == (4 + (to_integer(x0 as int32) * 4)));
  rewrite(to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) == ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32))));
  normalize();
 }
 have 65270 <= to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) by solve() using { to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == to_integer((4u32 + (x0 as uint32 * 4u32))) + to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))); 4 <= to_integer((4u32 + (x0 as uint32 * 4u32))); to_integer((4u32 + (x0 as uint32 * 4u32))) <= 1024; 65266 <= to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))); to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) <= 66541; };
 have to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) <= 67565 by solve() using { to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == to_integer((4u32 + (x0 as uint32 * 4u32))) + to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))); 4 <= to_integer((4u32 + (x0 as uint32 * 4u32))); to_integer((4u32 + (x0 as uint32 * 4u32))) <= 1024; 65266 <= to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))); to_integer(((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) <= 66541; };
 have to_integer(x2 as uint32) <= 1073741823 by solve() using { to_integer(x2 as uint32) <= 255; };
 have x2 as uint32 <= 4294967295u32 / 4u32 by solve() using { x2 as uint32 <= 1073741823u32; };
 have 4u32 == 0u32 or x2 as uint32 <= 4294967295u32 / 4u32 by assumption();
 apply(integer::uint32_multiply_to_integer(x2 as uint32, 4u32)) using { 4u32 == 0u32 or x2 as uint32 <= 4294967295u32 / 4u32; };
 have to_integer((x2 as uint32 * 4u32)) == (to_integer(x2 as int32) * 4) by {
  rewrite(to_integer((x2 as uint32 * 4u32)) == to_integer(x2 as uint32) * to_integer(4u32));
  rewrite(to_integer(x2 as uint32) == to_integer(x2 as int32));
  normalize();
 }
 have 0 <= to_integer((x2 as uint32 * 4u32)) by solve() using { to_integer((x2 as uint32 * 4u32)) == to_integer(x2 as uint32) * to_integer(4u32); 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer((x2 as uint32 * 4u32)) <= 1020 by solve() using { to_integer((x2 as uint32 * 4u32)) == to_integer(x2 as uint32) * to_integer(4u32); 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer(x2 as uint32) <= 65521 by solve() using { to_integer(x2 as uint32) <= 255; };
 have to_integer(65521u32 - (x2 as uint32)) == to_integer(65521u32) - to_integer((x2 as uint32));
 have to_integer((65521u32 - x2 as uint32)) == (65521 - to_integer(x2 as int32)) by {
  rewrite(to_integer((65521u32 - x2 as uint32)) == to_integer(65521u32) - to_integer(x2 as uint32));
  rewrite(to_integer(x2 as uint32) == to_integer(x2 as int32));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - x2 as uint32)) by solve() using { to_integer((65521u32 - x2 as uint32)) == to_integer(65521u32) - to_integer(x2 as uint32); 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer((65521u32 - x2 as uint32)) <= 65521 by solve() using { to_integer((65521u32 - x2 as uint32)) == to_integer(65521u32) - to_integer(x2 as uint32); 0 <= to_integer(x2 as uint32); to_integer(x2 as uint32) <= 255; };
 have to_integer((65521u32 - x2 as uint32)) <= 2147483647 by solve() using { to_integer((65521u32 - x2 as uint32)) <= 65521; };
 have (65521u32 - x2 as uint32) <= 4294967295u32 / 2u32 by solve() using { (65521u32 - x2 as uint32) <= 2147483647u32; };
 have 2u32 == 0u32 or (65521u32 - x2 as uint32) <= 4294967295u32 / 2u32 by assumption();
 have to_integer(((65521u32 - x2 as uint32)) * 2u32) == to_integer(((65521u32 - x2 as uint32))) * to_integer(2u32);
 have to_integer(((65521u32 - x2 as uint32) * 2u32)) == ((65521 - to_integer(x2 as int32)) * 2) by {
  rewrite(to_integer(((65521u32 - x2 as uint32) * 2u32)) == to_integer((65521u32 - x2 as uint32)) * to_integer(2u32));
  rewrite(to_integer((65521u32 - x2 as uint32)) == (65521 - to_integer(x2 as int32)));
  normalize();
 }
 have 130532 <= to_integer(((65521u32 - x2 as uint32) * 2u32)) by solve() using { to_integer(((65521u32 - x2 as uint32) * 2u32)) == to_integer((65521u32 - x2 as uint32)) * to_integer(2u32); 65266 <= to_integer((65521u32 - x2 as uint32)); to_integer((65521u32 - x2 as uint32)) <= 65521; };
 have to_integer(((65521u32 - x2 as uint32) * 2u32)) <= 131042 by solve() using { to_integer(((65521u32 - x2 as uint32) * 2u32)) == to_integer((65521u32 - x2 as uint32)) * to_integer(2u32); 65266 <= to_integer((65521u32 - x2 as uint32)); to_integer((65521u32 - x2 as uint32)) <= 65521; };
 have to_integer((x2 as uint32 * 4u32)) + to_integer(((65521u32 - x2 as uint32) * 2u32)) <= 4294967295 by solve() using { to_integer((x2 as uint32 * 4u32)) <= 1020; to_integer(((65521u32 - x2 as uint32) * 2u32)) <= 131042; };
 have to_integer((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)) == to_integer((x2 as uint32 * 4u32)) + to_integer(((65521u32 - x2 as uint32) * 2u32));
 have to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2)) by {
  rewrite(to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == to_integer((x2 as uint32 * 4u32)) + to_integer(((65521u32 - x2 as uint32) * 2u32)));
  rewrite(to_integer((x2 as uint32 * 4u32)) == (to_integer(x2 as int32) * 4));
  rewrite(to_integer(((65521u32 - x2 as uint32) * 2u32)) == ((65521 - to_integer(x2 as int32)) * 2));
  normalize();
 }
 have 130532 <= to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) by solve() using { to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == to_integer((x2 as uint32 * 4u32)) + to_integer(((65521u32 - x2 as uint32) * 2u32)); 0 <= to_integer((x2 as uint32 * 4u32)); to_integer((x2 as uint32 * 4u32)) <= 1020; 130532 <= to_integer(((65521u32 - x2 as uint32) * 2u32)); to_integer(((65521u32 - x2 as uint32) * 2u32)) <= 131042; };
 have to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) <= 132062 by solve() using { to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == to_integer((x2 as uint32 * 4u32)) + to_integer(((65521u32 - x2 as uint32) * 2u32)); 0 <= to_integer((x2 as uint32 * 4u32)); to_integer((x2 as uint32 * 4u32)) <= 1020; 130532 <= to_integer(((65521u32 - x2 as uint32) * 2u32)); to_integer(((65521u32 - x2 as uint32) * 2u32)) <= 131042; };
 have to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) + to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) <= 4294967295 by solve() using { to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) <= 67565; to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) <= 132062; };
 have to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) + to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)));
 have to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) == (((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))) + ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2))) by {
  rewrite(to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) == to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) + to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))));
  rewrite(to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) == ((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))));
  rewrite(to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) == ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2)));
  normalize();
 }
 have 195802 <= to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) by solve() using { to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) == to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) + to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))); 65270 <= to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))); to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) <= 67565; 130532 <= to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))); to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) <= 132062; };
 have to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) <= 199627 by solve() using { to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) == to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) + to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))); 65270 <= to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))); to_integer(((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32)))) <= 67565; 130532 <= to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))); to_integer(((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) <= 132062; };
 have to_integer(x3 as uint32) <= 1073741823 by solve() using { to_integer(x3 as uint32) <= 255; };
 have (x3 as uint32) <= 1073741823u32;
 have x3 as uint32 <= 4294967295u32 / 4u32 by solve() using { x3 as uint32 <= 1073741823u32; };
 have 4u32 == 0u32 or x3 as uint32 <= 4294967295u32 / 4u32 by assumption();
 have to_integer((x3 as uint32) * 4u32) == to_integer((x3 as uint32)) * to_integer(4u32);
 have to_integer((x3 as uint32 * 4u32)) == (to_integer(x3 as int32) * 4) by {
  rewrite(to_integer((x3 as uint32 * 4u32)) == to_integer(x3 as uint32) * to_integer(4u32));
  rewrite(to_integer(x3 as uint32) == to_integer(x3 as int32));
  normalize();
 }
 have 0 <= to_integer((x3 as uint32 * 4u32)) by solve() using { to_integer((x3 as uint32 * 4u32)) == to_integer(x3 as uint32) * to_integer(4u32); 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer((x3 as uint32 * 4u32)) <= 1020 by solve() using { to_integer((x3 as uint32 * 4u32)) == to_integer(x3 as uint32) * to_integer(4u32); 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer(x3 as uint32) <= 65521 by solve() using { to_integer(x3 as uint32) <= 255; };
 have (x3 as uint32) <= 65521u32;
 have to_integer(65521u32 - (x3 as uint32)) == to_integer(65521u32) - to_integer((x3 as uint32));
 have to_integer((65521u32 - x3 as uint32)) == (65521 - to_integer(x3 as int32)) by {
  rewrite(to_integer((65521u32 - x3 as uint32)) == to_integer(65521u32) - to_integer(x3 as uint32));
  rewrite(to_integer(x3 as uint32) == to_integer(x3 as int32));
  normalize();
 }
 have 65266 <= to_integer((65521u32 - x3 as uint32)) by solve() using { to_integer((65521u32 - x3 as uint32)) == to_integer(65521u32) - to_integer(x3 as uint32); 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer((65521u32 - x3 as uint32)) <= 65521 by solve() using { to_integer((65521u32 - x3 as uint32)) == to_integer(65521u32) - to_integer(x3 as uint32); 0 <= to_integer(x3 as uint32); to_integer(x3 as uint32) <= 255; };
 have to_integer((65521u32 - x3 as uint32)) <= 1431655765 by solve() using { to_integer((65521u32 - x3 as uint32)) <= 65521; };
 have to_integer((65521u32 - x3 as uint32)) <= to_integer(1431655765u32);
 have (65521u32 - x3 as uint32) <= 4294967295u32 / 3u32 by solve() using { (65521u32 - x3 as uint32) <= 1431655765u32; };
 have 3u32 == 0u32 or (65521u32 - x3 as uint32) <= 4294967295u32 / 3u32 by assumption();
 have to_integer(((65521u32 - x3 as uint32)) * 3u32) == to_integer(((65521u32 - x3 as uint32))) * to_integer(3u32);
 have to_integer(((65521u32 - x3 as uint32) * 3u32)) == ((65521 - to_integer(x3 as int32)) * 3) by {
  rewrite(to_integer(((65521u32 - x3 as uint32) * 3u32)) == to_integer((65521u32 - x3 as uint32)) * to_integer(3u32));
  rewrite(to_integer((65521u32 - x3 as uint32)) == (65521 - to_integer(x3 as int32)));
  normalize();
 }
 have 195798 <= to_integer(((65521u32 - x3 as uint32) * 3u32)) by solve() using { to_integer(((65521u32 - x3 as uint32) * 3u32)) == to_integer((65521u32 - x3 as uint32)) * to_integer(3u32); 65266 <= to_integer((65521u32 - x3 as uint32)); to_integer((65521u32 - x3 as uint32)) <= 65521; };
 have to_integer(((65521u32 - x3 as uint32) * 3u32)) <= 196563 by solve() using { to_integer(((65521u32 - x3 as uint32) * 3u32)) == to_integer((65521u32 - x3 as uint32)) * to_integer(3u32); 65266 <= to_integer((65521u32 - x3 as uint32)); to_integer((65521u32 - x3 as uint32)) <= 65521; };
 have to_integer((x3 as uint32 * 4u32)) + to_integer(((65521u32 - x3 as uint32) * 3u32)) <= 4294967295 by solve() using { to_integer((x3 as uint32 * 4u32)) <= 1020; to_integer(((65521u32 - x3 as uint32) * 3u32)) <= 196563; };
 have to_integer((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)) == to_integer((x3 as uint32 * 4u32)) + to_integer(((65521u32 - x3 as uint32) * 3u32));
 have to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == ((to_integer(x3 as int32) * 4) + ((65521 - to_integer(x3 as int32)) * 3)) by {
  rewrite(to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == to_integer((x3 as uint32 * 4u32)) + to_integer(((65521u32 - x3 as uint32) * 3u32)));
  rewrite(to_integer((x3 as uint32 * 4u32)) == (to_integer(x3 as int32) * 4));
  rewrite(to_integer(((65521u32 - x3 as uint32) * 3u32)) == ((65521 - to_integer(x3 as int32)) * 3));
  normalize();
 }
 have 195798 <= to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) by solve() using { to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == to_integer((x3 as uint32 * 4u32)) + to_integer(((65521u32 - x3 as uint32) * 3u32)); 0 <= to_integer((x3 as uint32 * 4u32)); to_integer((x3 as uint32 * 4u32)) <= 1020; 195798 <= to_integer(((65521u32 - x3 as uint32) * 3u32)); to_integer(((65521u32 - x3 as uint32) * 3u32)) <= 196563; };
 have to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) <= 197583 by solve() using { to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == to_integer((x3 as uint32 * 4u32)) + to_integer(((65521u32 - x3 as uint32) * 3u32)); 0 <= to_integer((x3 as uint32 * 4u32)); to_integer((x3 as uint32 * 4u32)) <= 1020; 195798 <= to_integer(((65521u32 - x3 as uint32) * 3u32)); to_integer(((65521u32 - x3 as uint32) * 3u32)) <= 196563; };
 have to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) + to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) <= 4294967295 by solve() using { to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) <= 199627; to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) <= 197583; };
 have to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) + to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)));
 have to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == ((((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))) + ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2))) + ((to_integer(x3 as int32) * 4) + ((65521 - to_integer(x3 as int32)) * 3))) by {
  rewrite(to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) + to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))));
  rewrite(to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) == (((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))) + ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2))));
  rewrite(to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) == ((to_integer(x3 as int32) * 4) + ((65521 - to_integer(x3 as int32)) * 3)));
  normalize();
 }
 have 391600 <= to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) by solve() using { to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) + to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))); 195802 <= to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))); to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) <= 199627; 195798 <= to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))); to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) <= 197583; };
 have to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) <= 397210 by solve() using { to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) + to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))); 195802 <= to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))); to_integer((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32)))) <= 199627; 195798 <= to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))); to_integer(((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) <= 197583; };
 have to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32) + to_integer(x3 as int32) by solve() using { to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == ((((1 + to_integer(x0 as int32)) + to_integer(x1 as int32)) + to_integer(x2 as int32)) + to_integer(x3 as int32)); };
 have to_integer((((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) % 65521u32) == truncating_remainder(to_integer((((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32))), to_integer(65521u32));
 have to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32) % 65521u32) == truncating_remainder(1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32) + to_integer(x3 as int32), 65521) by {
  rewrite(to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32) % 65521u32) == truncating_remainder(to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)), 65521));
  rewrite(to_integer(((((1u32 + x0 as uint32) + x1 as uint32) + x2 as uint32) + x3 as uint32)) == 1 + to_integer(x0 as int32) + to_integer(x1 as int32) + to_integer(x2 as int32) + to_integer(x3 as int32));
  normalize();
 }
 have to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126 by solve() using { to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == ((((4 + (to_integer(x0 as int32) * 4)) + ((to_integer(x1 as int32) * 4) + (65521 - to_integer(x1 as int32)))) + ((to_integer(x2 as int32) * 4) + ((65521 - to_integer(x2 as int32)) * 2))) + ((to_integer(x3 as int32) * 4) + ((65521 - to_integer(x3 as int32)) * 3))); };
 have to_integer((((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) % 65521u32) == truncating_remainder(to_integer((((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))))), to_integer(65521u32));
 have 0 <= 4 * to_integer(x0 as int32) by solve() using { 0 <= to_integer(x0 as int32); };
 have 0 <= 4 + 4 * to_integer(x0 as int32) by solve() using { 0 <= 4 * to_integer(x0 as int32); };
 have 0 <= 3 * to_integer(x1 as int32) by solve() using { 0 <= to_integer(x1 as int32); };
 have 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) by solve() using { 0 <= 3 * to_integer(x1 as int32); 0 <= 4 + 4 * to_integer(x0 as int32); };
 have 0 <= 2 * to_integer(x2 as int32) by solve() using { 0 <= to_integer(x2 as int32); };
 have 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) by solve() using { 0 <= 2 * to_integer(x2 as int32); 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32); };
 have 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) by solve() using { 0 <= to_integer(x3 as int32); 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32); };
 have 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126 by solve() using { 0 <= 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32); };
 have 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126 == (4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32)) + 65521 * 6 by solve() using {};
 apply(adler_residue_congruent(4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126, 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32), 6));
 have to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) % 65521u32) == truncating_remainder(4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32), 65521) by {
  rewrite(to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32))) % 65521u32) == truncating_remainder(to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))), 65521));
  rewrite(to_integer(((((4u32 + (x0 as uint32 * 4u32)) + ((x1 as uint32 * 4u32) + (65521u32 - x1 as uint32))) + ((x2 as uint32 * 4u32) + ((65521u32 - x2 as uint32) * 2u32))) + ((x3 as uint32 * 4u32) + ((65521u32 - x3 as uint32) * 3u32)))) == 4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126);
  rewrite(truncating_remainder(4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32) + 393126, 65521) == truncating_remainder(4 + 4 * to_integer(x0 as int32) + 3 * to_integer(x1 as int32) + 2 * to_integer(x2 as int32) + to_integer(x3 as int32), 65521));
  normalize();
 }
 assumption();
 }
}

theorem adler_four_byte_result_spec(bytes: uint8[]) {
 ensures to_integer(((((1u32 + bytes[0] as uint32) + bytes[1] as uint32) + bytes[2] as uint32) + bytes[3] as uint32) % 65521u32) == adler_spec_a(bytes, 4, 1) by {
  apply(adler_spec_four(bytes));
  apply(adler_four_byte_native_result(bytes[0], bytes[1], bytes[2], bytes[3]));
  rewrite(adler_spec_a(bytes, 4, 1) == truncating_remainder(1 + to_integer(bytes[0] as int32) + to_integer(bytes[1] as int32) + to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32), 65521));
  assumption();
 }
 ensures to_integer(((((4u32 + (bytes[0] as uint32 * 4u32)) + ((bytes[1] as uint32 * 4u32) + (65521u32 - bytes[1] as uint32))) + ((bytes[2] as uint32 * 4u32) + ((65521u32 - bytes[2] as uint32) * 2u32))) + ((bytes[3] as uint32 * 4u32) + ((65521u32 - bytes[3] as uint32) * 3u32))) % 65521u32) == adler_spec_b(bytes, 4, 1, 0) by {
  apply(adler_spec_four(bytes));
  apply(adler_four_byte_native_result(bytes[0], bytes[1], bytes[2], bytes[3]));
  rewrite(adler_spec_b(bytes, 4, 1, 0) == truncating_remainder(4 + 4 * to_integer(bytes[0] as int32) + 3 * to_integer(bytes[1] as int32) + 2 * to_integer(bytes[2] as int32) + to_integer(bytes[3] as int32), 65521));
  assumption();
 }
}
