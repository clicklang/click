# A 64-bit range needs no bound on its length

The contracts of `a_64_bit_index_and_bound_need_no_cast.md` without
`requires length <= 2147483647`. A range whose bound is a `size_t` has
64-bit bounds, and an access at a `size_t` index is placed in it by 64-bit
comparisons, so nothing has to fit 32 bits. What the range does state is
the object-size limit, `length <= 9223372036854775807`, which holds of any
object and is assumed where a contract holds the range on entry.

This contract used to be refused, asking for the 32-bit bound.

```c filename=a_64_bit_range_needs_no_bound_on_its_length.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
void write(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index] = value;
}
```

```click
verifying "a_64_bit_range_needs_no_bound_on_its_length.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index < length;
    views bytes[0..length];
    ensures result == bytes[index];
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index, uint8 value) {
    requires index < length;
    owns bytes[0..length];
    ensures bytes[index] == value;
} by { execute(); simp(); }
```

```expect
pass
```
