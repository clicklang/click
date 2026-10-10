# A window two offsets into a 64-bit range

`first_of_four(chunk + index)` where `chunk` is itself `bytes + start`: a
chunk of a chunk. The callee's four bytes start at element `start + index`
of `bytes[0..length]`. The two `size_t` offsets are read as that one index
when their sum cannot wrap, which is decided as each being at most
`9223372036854775807`, and the window is then covered as in
`a_callee_takes_a_window_of_a_64_bit_range.md`: `start + index <= length`
and `4 <= length - (start + index)`.

`a_window_two_offsets_past_the_end_is_refused.md` leaves one element out.

```c filename=a_window_two_offsets_into_a_64_bit_range.c
unsigned char first_of_four(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long start, unsigned long index) {
    const unsigned char *chunk = bytes + start;
    return first_of_four(chunk + index);
}
```

```click
verifying "a_window_two_offsets_into_a_64_bit_range.c";
uint8 first_of_four(const uint8* chunk) {
    views chunk[0..4];
    ensures result == chunk[0];
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, uint64 start, uint64 index) {
    requires length <= 2147483647u64;
    requires start <= length;
    requires index <= length - start;
    requires 4u64 <= (length - start) - index;
    views bytes[0..length];
    ensures result == result;
} by {
    have start <= 9223372036854775807u64 by { arithmetic() using { start <= length; length <= 2147483647u64; } }
    have index <= length by { arithmetic() using { index <= length - start; start <= length; } }
    have index <= 9223372036854775807u64 by { arithmetic() using { index <= length; length <= 2147483647u64; } }
    have start + index <= length by { arithmetic() using { index <= length - start; start <= length; } }
    have 4u64 <= length - (start + index) by { arithmetic() using { 4u64 <= (length - start) - index; index <= length - start; start <= length; } }
    execute(); simp();
}
```

```expect
pass
```
