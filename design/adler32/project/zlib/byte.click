import click::integer;

theorem zlib_byte_u64(value: uint8) {
 ensures to_integer(value) <= 255 by {
  have 0 <= value as int32 by { close(); }
  have value as int32 <= 255 by { close(); }
  have to_integer(value) == to_integer(value as int32) by {
   close() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; };
  }
  close() using { to_integer(value) == to_integer(value as int32); to_integer(value as int32) <= 255; };
 }
 ensures value as uint64 <= 255u64 by {
  have 0 <= value as int32 by { close(); }
  have value as int32 <= 255 by { close(); }
  have to_integer(value as uint64) == to_integer(value as int32) by { close() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; }; }
  have to_integer(value as uint64) <= to_integer(255u64) by { close() using {
   to_integer(value as uint64) == to_integer(value as int32);
   to_integer(value as int32) <= to_integer(255);
  }; }
  close();
 }
 ensures value as uint32 as uint64 <= 255u64 by {
  have 0 <= value as int32 by { close(); }
  have value as int32 <= 255 by { close(); }
  have to_integer(value as uint32) == to_integer(value as int32) by { close() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; }; }
  have 0 <= to_integer(value as uint32) by { rewrite(to_integer(value as uint32), to_integer(value as int32)); close(); }
  have to_integer(value as uint32) <= 255 by { rewrite(to_integer(value as uint32), to_integer(value as int32)); close(); }
  have to_integer(value as uint32 as uint64) == to_integer(value as uint32) by { close() using { 0 <= to_integer(value as uint32); to_integer(value as uint32) <= 255; }; }
  have to_integer(value as uint32 as uint64) <= to_integer(255u64) by { close() using {
   to_integer(value as uint32 as uint64) == to_integer(value as uint32); to_integer(value as uint32) <= 255;
  }; }
  close();
 }
 ensures to_integer(value as uint32 as uint64) == to_integer(value as int32) by {
  have 0 <= value as int32 by { close(); }
  have value as int32 <= 255 by { close(); }
  have to_integer(value as uint32) == to_integer(value as int32) by { close() using { 0 <= to_integer(value as int32); to_integer(value as int32) <= 255; }; }
  have 0 <= to_integer(value as uint32) by { rewrite(to_integer(value as uint32), to_integer(value as int32)); close(); }
  have to_integer(value as uint32) <= 255 by { rewrite(to_integer(value as uint32), to_integer(value as int32)); close(); }
  have to_integer(value as uint32 as uint64) == to_integer(value as uint32) by { close() using { 0 <= to_integer(value as uint32); to_integer(value as uint32) <= 255; }; }
  close() using { to_integer(value as uint32 as uint64) == to_integer(value as uint32); to_integer(value as uint32) == to_integer(value as int32); };
 }

 ensures 0 <= to_integer(value as int32) by {
  have 0 <= value as int32 by { close(); }
  close();
 }
 ensures to_integer(value as int32) <= 255 by {
  have value as int32 <= 255 by { close(); }
  close();
 }

}
