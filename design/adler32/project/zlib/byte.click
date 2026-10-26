import click::integer;

theorem zlib_byte_u64(value: uint8) {
 ensures to_integer(value) <= 255 by {
  have 0 <= value as int32 by { solve(); }
  have value as int32 <= 255 by { solve(); }
  have value as int32 as uint8 == value by { solve(); }
  have to_integer(value as int32 as uint8) == to_integer(value as int32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as int32 as uint8) == to_integer(value as int32); conclusion 0;
  } }
  have to_integer(value) == to_integer(value as int32) by { rewrite(value == value as int32 as uint8); normalize(); }
  solve() using { to_integer(value) == to_integer(value as int32); to_integer(value as int32) <= 255; };
 }
 ensures value as uint64 <= 255u64 by {
  have 0 <= value as int32 by { solve(); }
  have value as int32 <= 255 by { solve(); }
  have to_integer(value as uint64) == to_integer(value as int32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint64) == to_integer(value as int32); conclusion 0;
  } }
  have to_integer(value as uint64) <= to_integer(255u64) by { solve() using {
   to_integer(value as uint64) == to_integer(value as int32);
   to_integer(value as int32) <= to_integer(255);
  }; }
  assumption();
 }
 ensures value as uint32 as uint64 <= 255u64 by {
  have 0 <= value as int32 by { solve(); }
  have value as int32 <= 255 by { solve(); }
  have to_integer(value as uint32) == to_integer(value as int32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32) == to_integer(value as int32); conclusion 0;
  } }
  have 0 <= to_integer(value as uint32) by { rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption(); }
  have to_integer(value as uint32) <= 255 by { rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption(); }
  have to_integer(value as uint32 as uint64) == to_integer(value as uint32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as uint32) => 0 <= to_integer(value as uint32);
   premise 1: to_integer(value as uint32) <= 255 => to_integer(value as uint32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32 as uint64) == to_integer(value as uint32); conclusion 0;
  } }
  have to_integer(value as uint32 as uint64) <= to_integer(255u64) by { solve() using {
   to_integer(value as uint32 as uint64) == to_integer(value as uint32); to_integer(value as uint32) <= 255;
  }; }
  assumption();
 }
 ensures to_integer(value as uint32 as uint64) == to_integer(value as int32) by {
  have 0 <= value as int32 by { solve(); }
  have value as int32 <= 255 by { solve(); }
  have to_integer(value as uint32) == to_integer(value as int32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as int32) => 0 <= to_integer(value as int32);
   premise 1: to_integer(value as int32) <= 255 => to_integer(value as int32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32) == to_integer(value as int32); conclusion 0;
  } }
  have 0 <= to_integer(value as uint32) by { rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption(); }
  have to_integer(value as uint32) <= 255 by { rewrite(to_integer(value as uint32) == to_integer(value as int32)); assumption(); }
  have to_integer(value as uint32 as uint64) == to_integer(value as uint32) by { arithmetic_certificate rules {
   premise 0: 0 <= to_integer(value as uint32) => 0 <= to_integer(value as uint32);
   premise 1: to_integer(value as uint32) <= 255 => to_integer(value as uint32) <= 255;
   integer_cast_identity bounds [0, 1] => to_integer(value as uint32 as uint64) == to_integer(value as uint32); conclusion 0;
  } }
  solve() using { to_integer(value as uint32 as uint64) == to_integer(value as uint32); to_integer(value as uint32) == to_integer(value as int32); };
 }

 ensures 0 <= to_integer(value as int32) by {
  have 0 <= value as int32 by { solve(); }
  assumption();
 }
 ensures to_integer(value as int32) <= 255 by {
  have value as int32 <= 255 by { solve(); }
  assumption();
 }

}
