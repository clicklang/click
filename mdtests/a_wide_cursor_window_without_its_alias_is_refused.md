# An unbound cursor cannot borrow a wide window

The cursor has no checked equality to the input range. Bounds on an unrelated
index cannot supply authority for its call.

```c filename=a_wide_cursor_window_without_its_alias_is_refused.c
unsigned char first(const unsigned char *chunk) { return chunk[0]; }
unsigned char read(const unsigned char *bytes, unsigned long length, const unsigned char *cursor, unsigned long index) {
    return first(cursor);
}
```

```click
verifying "a_wide_cursor_window_without_its_alias_is_refused.c";
uint8 first(const uint8* chunk) {
    views chunk[0..4];
    ensures result == old(chunk[0]);
} by { execute(); simp(); }
uint8 read(const uint8* bytes, uint64 length, const uint8* cursor, uint64 index) {
    requires index <= length;
    requires 4u64 <= length - index;
    views bytes[0..length];
    ensures result == old(cursor[0]);
} by { execute(); simp(); }
```

```expect
fail: stable-view
```
