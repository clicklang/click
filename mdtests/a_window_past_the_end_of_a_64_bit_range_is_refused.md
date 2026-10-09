# A window past the end of a 64-bit range is refused

The call of `a_callee_takes_a_window_of_a_64_bit_range.md` with only three
elements known to remain after `index`. The callee's four-byte window may
reach one element past `bytes[0..length]`, so the call is refused.

```c filename=a_window_past_the_end_of_a_64_bit_range_is_refused.c
unsigned char first_of_four(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return first_of_four(bytes + index);
}
```

```click
verifying "a_window_past_the_end_of_a_64_bit_range_is_refused.c";
uint8 first_of_four(const uint8* chunk) {
    views chunk[0..4];
    ensures result == chunk[0];
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index <= length;
    requires 3u64 <= length - index;
    views bytes[0..length];
    ensures result == bytes[index];
} by { execute(); simp(); }
```

```expect
fail: selected resource `views bytes[index..(index + 4)]`
```
