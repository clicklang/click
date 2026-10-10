# A checked cursor cannot borrow past the wide endpoint

The cursor equals the indexed input address, but the supplied guard guarantees
only three bytes. The four-byte callee window remains unauthorized.

```c filename=a_wide_cursor_window_without_its_extent_is_refused.c
unsigned char first(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, const unsigned char *cursor, unsigned long index) {
    return first(cursor);
}
```

```click
verifying "a_wide_cursor_window_without_its_extent_is_refused.c";
uint8 first(const uint8* chunk) {
    views chunk[0..4];
    ensures result == old(chunk[0]);
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, const uint8* cursor, uint64 index) {
    requires index <= length;
    requires 3u64 <= length - index;
    requires cursor == bytes + index;
    views bytes[0..length];
    ensures result == old(cursor[0]);
} by { execute(); simp(); }
```

```expect
fail: stable-view
```
