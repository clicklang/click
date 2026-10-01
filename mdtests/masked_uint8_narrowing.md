# Masked unsigned byte narrowing has intrinsic bounds

Masking a word with 255 clears the sign bit and bounds it by 255. Both
narrowing prerequisites follow from that expression's shape alone.

```c filename=masked_uint8_narrowing.c
unsigned char low_byte(unsigned value) {
    return (unsigned char)(int)(value & 255u);
}
```

```click
verifying "masked_uint8_narrowing.c";
uint8 low_byte(uint32 value) {
    ensures ((uint32)result) == (value & 255u32);
} by { execute(); simp(); }
```

```expect
pass
```
