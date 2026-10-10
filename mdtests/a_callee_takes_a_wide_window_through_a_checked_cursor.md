# A callee takes a wide window through a checked cursor

A stored cursor has a separate symbolic address. Its checked equality to
`bytes + index` lets the callee borrow the same four-byte window as a direct
indexed call, while the native difference guard excludes a wrapping endpoint.

```c filename=a_callee_takes_a_wide_window_through_a_checked_cursor.c
unsigned char first(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, const unsigned char *cursor, unsigned long index) {
    return first(cursor);
}
```

```click
verifying "a_callee_takes_a_wide_window_through_a_checked_cursor.c";
uint8 first(const uint8* chunk) {
    views chunk[0..4];
    ensures result == old(chunk[0]);
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, const uint8* cursor, uint64 index) {
    requires index <= length;
    requires 4u64 <= length - index;
    requires cursor == bytes + index;
    views bytes[0..length];
    ensures result == old(cursor[0]);
} by { execute(); simp(); }
```

```expect
pass
```
