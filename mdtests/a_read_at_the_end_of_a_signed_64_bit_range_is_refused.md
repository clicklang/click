# A read at the end of a signed 64-bit range is refused

`bytes[0..n]` with `long n` does not hold `bytes[n]`, as in
`a_range_with_a_signed_or_int32_bound_is_64_bit.md` but one element higher.

```c filename=a_read_at_the_end_of_a_signed_64_bit_range_is_refused.c
unsigned char past(const unsigned char *bytes, long n) { return bytes[n]; }
```

```click
verifying "a_read_at_the_end_of_a_signed_64_bit_range_is_refused.c";
uint8 past(const uint8* bytes, int64 n) {
    requires 0i64 < n;
    views bytes[0..n];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views bytes[n]`
```
