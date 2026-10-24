# `auto` widens a narrow value into a containing type

An 8- or 16-bit value's word is the canonical carrier of its type, its sign
or zero extension, so a type of at most 32 bits that contains the narrow
type reads the same value from the same word. `auto` proves
`to_integer(result) == to_integer(x)` for each such C widening of a narrow
parameter, with no premise. The 64-bit widenings are
[`auto_widens_a_narrow_value_to_64_bits.md`](auto_widens_a_narrow_value_to_64_bits.md),
and the negatives are
[`a_narrowing_conversion_without_its_range_is_not_its_operand.md`](a_narrowing_conversion_without_its_range_is_not_its_operand.md)
and
[`a_sign_changing_conversion_of_a_narrow_value_is_not_a_widening.md`](a_sign_changing_conversion_of_a_narrow_value_is_not_a_widening.md).

```c filename=widen.c
short s8_16(signed char x) { return x; }
int s8_32(signed char x) { return x; }
unsigned short u8_u16(unsigned char x) { return x; }
short u8_s16(unsigned char x) { return x; }
int u16_s32(unsigned short x) { return x; }
unsigned int u16_u32(unsigned short x) { return x; }
```

```click
verifying "widen.c";

short s8_16(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }

int s8_32(signed char x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }

unsigned short u8_u16(unsigned char x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }

short u8_s16(unsigned char x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }

int u16_s32(unsigned short x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }

unsigned int u16_u32(unsigned short x) {
    ensures to_integer(result) == to_integer(x);
} by { execute(); auto(); }
```

```expect
pass
```
