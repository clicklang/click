# A 64-bit index plus a constant is in range

`next` reads `bytes[index + 1]` with a `size_t` index. The contract bounds
the sum, `index + 1 < length`, in the type the C has. The place is written
the same way, `bytes[index + 1u64]`, and the read is at that 64-bit index:
the sum is below `length`, so it does not wrap and lies in the range.

`a_64_bit_index_plus_a_constant_past_its_bound_is_refused.md` bounds only
`index`.

```c filename=a_64_bit_index_plus_a_constant_is_in_range.c
unsigned char next(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index + 1];
}
void set_next(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index + 1] = value;
}
```

```click
verifying "a_64_bit_index_plus_a_constant_is_in_range.c";
uint8 next(const uint8* bytes, uint64 length, uint64 index) {
    requires index + 1u64 < length;
    views bytes[0..length];
    ensures result == bytes[index + 1u64];
} by { execute(); simp(); }
void set_next(uint8* bytes, uint64 length, uint64 index, uint8 value) {
    requires index + 1u64 < length;
    owns bytes[0..length];
    ensures bytes[index + 1u64] == value;
} by { execute(); simp(); }
```

```expect
pass
```
