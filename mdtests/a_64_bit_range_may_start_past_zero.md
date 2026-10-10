# A 64-bit range may start past zero

A range with a `size_t` bound keeps 64-bit bounds whatever its start: a
symbolic `size_t` start, `bytes[start..length]`, an integer literal beside
the 64-bit bound, `bytes[1..length]` and `bytes[index..4]`, and a start
written as a sum, `bytes[index + 1u64..length]`. Nothing is cast and no
bound on `length` is stated. A caller holding `bytes[0..length]` covers a
callee's `bytes[1..length]`.

`a_read_below_a_64_bit_range_start_is_refused.md` reads the element just
before the start.

```c filename=a_64_bit_range_may_start_past_zero.c
unsigned char second(const unsigned char *bytes, unsigned long length) { return bytes[1]; }
unsigned char at(const unsigned char *bytes, unsigned long start, unsigned long length) { return bytes[start]; }
unsigned char in_four(const unsigned char *bytes, unsigned long index) { return bytes[index]; }
unsigned char next(const unsigned char *bytes, unsigned long index, unsigned long length) { return bytes[index + 1]; }
unsigned char whole(const unsigned char *bytes, unsigned long length) { return second(bytes, length); }
```

```click
verifying "a_64_bit_range_may_start_past_zero.c";
uint8 second(const uint8* bytes, uint64 length) {
    requires 1u64 < length;
    views bytes[1..length];
    ensures result == bytes[1];
} by { execute(); simp(); }
uint8 at(const uint8* bytes, uint64 start, uint64 length) {
    requires start < length;
    views bytes[start..length];
    ensures result == bytes[start];
} by { execute(); simp(); }
uint8 in_four(const uint8* bytes, uint64 index) {
    requires index < 4u64;
    views bytes[index..4];
    ensures result == bytes[index];
} by { execute(); simp(); }
uint8 next(const uint8* bytes, uint64 index, uint64 length) {
    requires index + 1u64 < length;
    views bytes[index + 1u64..length];
    ensures result == bytes[index + 1u64];
} by { execute(); simp(); }
uint8 whole(const uint8* bytes, uint64 length) {
    requires 1u64 < length;
    views bytes[0..length];
    ensures result == bytes[1];
} by { execute(); simp(); }
```

```expect
pass
```
