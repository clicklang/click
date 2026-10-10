# A range with a signed or `int32` bound beside a 64-bit one is 64-bit

A range keeps 64-bit bounds when one bound is a 64-bit term, signed or
unsigned: `bytes[i..length]` with an `int` start and a `size_t` end,
`bytes[0..n]` and `bytes[i..n]` with `long` bounds. A signed bound is read
as its sign extension, so a negative one lies past every range's end and
the range's own guards rule it out; nothing is cast and no bound on the
length is stated. A caller holding `bytes[0..n]` covers the callee's
`bytes[0..n]`.

`a_read_at_the_end_of_a_signed_64_bit_range_is_refused.md` reads one
element too far, and `a_call_hands_over_a_range_in_order.md` passes a
negative start.

```c filename=a_range_with_a_signed_or_int32_bound_is_64_bit.c
unsigned char at(const unsigned char *bytes, int i, unsigned long length) { return bytes[i]; }
unsigned char first(const unsigned char *bytes, long n) { return bytes[0]; }
unsigned char within(const unsigned char *bytes, long i, long n) { return bytes[i]; }
unsigned char whole(const unsigned char *bytes, long n) { return first(bytes, n); }
```

```click
verifying "a_range_with_a_signed_or_int32_bound_is_64_bit.c";
uint8 at(const uint8* bytes, int32 i, uint64 length) {
    requires (uint64)i < length;
    views bytes[i..length];
    ensures result == bytes[i];
} by { execute(); simp(); }
uint8 first(const uint8* bytes, int64 n) {
    requires 0i64 < n;
    views bytes[0..n];
    ensures result == bytes[0];
} by { execute(); simp(); }
uint8 within(const uint8* bytes, int64 i, int64 n) {
    requires 0i64 <= i;
    requires i < n;
    views bytes[i..n];
    ensures result == bytes[i];
} by { execute(); simp(); }
uint8 whole(const uint8* bytes, int64 n) {
    requires 0i64 < n;
    views bytes[0..n];
} by { execute(); simp(); }
```

```expect
pass
```
