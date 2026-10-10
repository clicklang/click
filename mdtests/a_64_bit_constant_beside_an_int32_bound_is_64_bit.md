# A 64-bit constant beside an `int32` bound is 64-bit

A range is 64-bit when either bound is a 64-bit integer, a constant
included: `bytes[i..4294967296u64]` with an `int` start is read with the
start's sign extension, as `bytes[i..length]` is in
`a_range_with_a_signed_or_int32_bound_is_64_bit.md`. Nothing converts the
end to 32 bits, where 2^32 would not fit.

```c filename=a_64_bit_constant_beside_an_int32_bound_is_64_bit.c
unsigned char at(const unsigned char *bytes, int i) { return bytes[i]; }
```

```click
verifying "a_64_bit_constant_beside_an_int32_bound_is_64_bit.c";
uint8 at(const uint8* bytes, int32 i) {
    requires (uint64)i < 4294967296u64;
    views bytes[i..4294967296u64];
    ensures result == bytes[i];
} by { execute(); simp(); }
```

```expect
pass
```
