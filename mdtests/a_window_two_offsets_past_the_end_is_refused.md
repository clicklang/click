# A window two offsets past the end is refused

`first_of_four(chunk + index)` where `chunk` is itself `bytes + start`, with
only three elements known to remain after `start + index`. The callee's four bytes
may reach one element past `bytes[0..length]`, so the call is refused.

```c filename=a_window_two_offsets_past_the_end_is_refused.c
unsigned char first_of_four(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, unsigned long start, unsigned long index) {
    const unsigned char *chunk = bytes + start;
    return first_of_four(chunk + index);
}
```

```click
verifying "a_window_two_offsets_past_the_end_is_refused.c";
uint8 first_of_four(const uint8* chunk) {
    views chunk[0..4];
    ensures result == chunk[0];
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, uint64 start, uint64 index) {
    requires length <= 2147483647u64;
    requires start <= length;
    requires index <= length - start;
    requires 3u64 <= (length - start) - index;
    views bytes[0..length];
    ensures result == result;
} by {
    have start <= 9223372036854775807u64 by { arithmetic() using { start <= length; length <= 2147483647u64; } }
    have index <= length by { arithmetic() using { index <= length - start; start <= length; } }
    have index <= 9223372036854775807u64 by { arithmetic() using { index <= length; length <= 2147483647u64; } }
    have start + index <= length by { arithmetic() using { index <= length - start; start <= length; } }
    have 3u64 <= length - (start + index) by { arithmetic() using { 3u64 <= (length - start) - index; index <= length - start; start <= length; } }
    execute(); simp();
}
```

```expect
fail: the required loan backing or binding is missing
```
