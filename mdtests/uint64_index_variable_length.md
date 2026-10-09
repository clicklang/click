# A uint64 index below a bounded variable length accesses the same byte

The index and length keep their 64-bit types in the contract, as in the C.
The range `bytes[0..length]` has 64-bit bounds and `bytes[index]` is the
element at that index, so no cast is written and no bound on `length` is
needed.

`a_cast_in_a_place_reads_the_truncated_index.md` writes a cast in the place.

```c filename=uint64_index_variable_length.c
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return bytes[index];
}
void write(unsigned char *bytes, unsigned long length, unsigned long index, unsigned char value) {
    bytes[index] = value;
}
```

```click
verifying "uint64_index_variable_length.c";
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
