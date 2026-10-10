# A read below a 64-bit range's start is refused

`bytes[1..length]` does not hold `bytes[0]`, as in
`a_64_bit_range_may_start_past_zero.md` but one element lower.

```c filename=a_read_below_a_64_bit_range_start_is_refused.c
unsigned char below(const unsigned char *bytes, unsigned long length) { return bytes[0]; }
```

```click
verifying "a_read_below_a_64_bit_range_start_is_refused.c";
uint8 below(const uint8* bytes, uint64 length) {
    requires 1u64 < length;
    views bytes[1..length];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views bytes[0]`
```
