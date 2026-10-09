# A 64-bit index plus a constant past its bound is refused

`next` reads `bytes[index + 1]`, and the contract bounds `index` alone.
`index` may be `length - 1`, so the read may be one past the range.

`a_64_bit_index_plus_a_constant_is_in_range.md` bounds the sum.

```c filename=a_64_bit_index_plus_a_constant_past_its_bound_is_refused.c
unsigned char next(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index + 1];
}
```

```click
verifying "a_64_bit_index_plus_a_constant_past_its_bound_is_refused.c";
uint8 next(const uint8* bytes, uint64 length, uint64 index) {
    requires length <= 2147483647u64;
    requires index < length;
    views bytes[0..length];
    ensures result == result;
} by { execute(); simp(); }
```

```expect
fail: missing resource fact
```
