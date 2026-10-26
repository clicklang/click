import click::integer;

theorem zlib_byte_u64(value: uint8) {
 ensures to_integer(value) <= 255 by {
  have 0 <= (int32)value by { solve(); }
  have (int32)value <= 255 by { solve(); }
  have (uint8)(int32)value == value by { solve(); }
  have to_integer((uint8)(int32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint8)(int32)value) == to_integer((int32)value); conclusion 0;
  } }
  have to_integer(value) == to_integer((int32)value) by { rewrite(value == (uint8)(int32)value); normalize(); }
  solve() using { to_integer(value) == to_integer((int32)value); to_integer((int32)value) <= 255; };
 }
 ensures (uint64)value <= 255u64 by {
  have 0 <= (int32)value by { solve(); }
  have (int32)value <= 255 by { solve(); }
  have to_integer((uint64)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)value) == to_integer((int32)value); conclusion 0;
  } }
  have to_integer((uint64)value) <= to_integer(255u64) by { solve() using {
   to_integer((uint64)value) == to_integer((int32)value);
   to_integer((int32)value) <= to_integer(255);
  }; }
  assumption();
 }
 ensures (uint64)(uint32)value <= 255u64 by {
  have 0 <= (int32)value by { solve(); }
  have (int32)value <= 255 by { solve(); }
  have to_integer((uint32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value); conclusion 0;
  } }
  have 0 <= to_integer((uint32)value) by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint32)value) <= 255 by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint64)(uint32)value) == to_integer((uint32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((uint32)value) => 0 <= to_integer((uint32)value);
   premise 1: to_integer((uint32)value) <= 255 => to_integer((uint32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)(uint32)value) == to_integer((uint32)value); conclusion 0;
  } }
  have to_integer((uint64)(uint32)value) <= to_integer(255u64) by { solve() using {
   to_integer((uint64)(uint32)value) == to_integer((uint32)value); to_integer((uint32)value) <= 255;
  }; }
  assumption();
 }
 ensures to_integer((uint64)(uint32)value) == to_integer((int32)value) by {
  have 0 <= (int32)value by { solve(); }
  have (int32)value <= 255 by { solve(); }
  have to_integer((uint32)value) == to_integer((int32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((int32)value) => 0 <= to_integer((int32)value);
   premise 1: to_integer((int32)value) <= 255 => to_integer((int32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint32)value) == to_integer((int32)value); conclusion 0;
  } }
  have 0 <= to_integer((uint32)value) by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint32)value) <= 255 by { rewrite(to_integer((uint32)value) == to_integer((int32)value)); assumption(); }
  have to_integer((uint64)(uint32)value) == to_integer((uint32)value) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer((uint32)value) => 0 <= to_integer((uint32)value);
   premise 1: to_integer((uint32)value) <= 255 => to_integer((uint32)value) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer((uint64)(uint32)value) == to_integer((uint32)value); conclusion 0;
  } }
  solve() using { to_integer((uint64)(uint32)value) == to_integer((uint32)value); to_integer((uint32)value) == to_integer((int32)value); };
 }

 ensures 0 <= to_integer((int32)value) by {
  have 0 <= (int32)value by { solve(); }
  assumption();
 }
 ensures to_integer((int32)value) <= 255 by {
  have (int32)value <= 255 by { solve(); }
  assumption();
 }

}
