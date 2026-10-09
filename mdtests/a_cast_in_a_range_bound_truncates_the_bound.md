# A cast in a range bound truncates the bound

`bytes[0..(int32)length]` is legal and means what it says: the range up to
the length truncated to 32 bits, read through 32-bit indices. The C reads
`bytes[index]` at the 64-bit index, which that range is not shown to hold,
even with the length known to fit: an index is never narrowed to meet a
range. This is the rule for a cast in a place,
`a_cast_in_a_place_reads_the_truncated_index.md`.

Write the bound as the C has it, as
`a_64_bit_range_needs_no_bound_on_its_length.md` does.

```c filename=a_cast_in_a_range_bound_truncates_the_bound.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
```

```click
verifying "a_cast_in_a_range_bound_truncates_the_bound.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires length <= 2147483647u64;
    requires index < length;
    views bytes[0..(int32)length];
    ensures result == bytes[index];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `views bytes[index]`
```
