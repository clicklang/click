# A nine-bit mask cannot justify byte narrowing

Masking with 511 clears the sign bit but permits values above 255.
The byte narrowing upper bound must fail.

```c filename=masked_uint8_narrowing.c
unsigned char low_byte(unsigned value) {
    return (unsigned char)(int)(value & 511u);
}
```

```click
verifying "masked_uint8_narrowing.c";
uint8 low_byte(uint32 value) {
    ensures ((uint32)result) == (value & 511u32);
} by { execute(); simp(); }
```

```expect
fail: uint8 narrowing upper bound
```
