# A 64-bit index and bound need no cast

`read` and `write` take a `size_t` length and index. Their contracts name the
range `bytes[0..length]` and the element `bytes[index]` in the types the C
has. A place takes a 32-bit index, so each is converted as the cast
`(int32)length` converts it, and the requirement `length <= 2147483647` is
what makes the conversion exact.

`uint64_index_variable_length.md` is the same pair with the casts written.
`a_64_bit_bound_must_be_shown_to_fit_a_32_bit_index.md` leaves the
requirement out.

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
