# A callee takes a window of a 64-bit range

`first_of_four(bytes + index)` hands the callee four bytes that start at a
`size_t` index of a range with a `size_t` bound. The callee's
`views chunk[0..4]` is covered by the caller's `views bytes[0..length]` when
the four elements from `index` lie inside it: `index <= length` and
`4 <= length - index`, both 64-bit comparisons. The second is written as a
difference so that no sum can wrap. Nothing is cast and no bound on
`length` is stated.

`a_window_past_the_end_of_a_64_bit_range_is_refused.md` leaves one element
out.

```c filename=a_callee_takes_a_window_of_a_64_bit_range.c
unsigned char first_of_four(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long index) {
    return first_of_four(bytes + index);
}
```

```click
verifying "a_callee_takes_a_window_of_a_64_bit_range.c";
uint8 first_of_four(const uint8* chunk) {
    views chunk[0..4];
    ensures result == chunk[0];
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, uint64 index) {
    requires index <= length;
    requires 4u64 <= length - index;
    views bytes[0..length];
    ensures result == bytes[index];
} by { execute(); simp(); }
```

```expect
pass
```
