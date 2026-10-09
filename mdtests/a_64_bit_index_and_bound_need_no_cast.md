# A 64-bit index and bound need no cast

`read` and `write` take a `size_t` length and index. Their contracts name the
range `bytes[0..length]` and the element `bytes[index]` in the types the C
has, and both are read at their 64-bit values. The requirement
`length <= 2147483647` is not needed for that; it is kept here as a
contract that states more than it must.

`a_64_bit_range_needs_no_bound_on_its_length.md` leaves the requirement
out.

```c filename=a_64_bit_index_and_bound_need_no_cast.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
void write(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index] = value;
}
```

```click
verifying "a_64_bit_index_and_bound_need_no_cast.c";
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires length <= 2147483647u64;
    requires index < length;
    views bytes[0..length];
    ensures result == bytes[index];
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index, uint8 value) {
    requires length <= 2147483647u64;
    requires index < length;
    owns bytes[0..length];
    ensures bytes[index] == value;
} by { execute(); simp(); }
```

```expect
pass
```
