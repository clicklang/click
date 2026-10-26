# The implicit closer widens a narrow value to 64 bits

A 64-bit type that contains an 8- or 16-bit type reads the narrow value
from the sign extension of its word, or for an unsigned value from its
zero extension, since the word is the value's canonical carrier. The
32-bit widenings are
[`auto_widens_a_narrow_value_into_a_containing_type.md`](auto_widens_a_narrow_value_into_a_containing_type.md).

```c filename=widen64.c
long s8_64(signed char x) { return x; }
long s16_64(short x) { return x; }
unsigned long u8_u64(unsigned char x) { return x; }
long u16_s64(unsigned short x) { return x; }
```

```click
verifying "widen64.c";

long s8_64(signed char x) {
    ensures to_integer(result) == to_integer(x);
}

long s16_64(short x) {
    ensures to_integer(result) == to_integer(x);
}

unsigned long u8_u64(unsigned char x) {
    ensures to_integer(result) == to_integer(x);
}

long u16_s64(unsigned short x) {
    ensures to_integer(result) == to_integer(x);
}
```

```expect
pass
```
