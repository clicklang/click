# An owned window past the end of a 64-bit range is refused

As `a_callee_owns_a_window_of_a_64_bit_range.md`, but the caller knows only
that three elements follow `index`: the callee's fourth byte lies past
`bytes[0..length]`, and the call is refused.

```c filename=an_owned_window_past_the_end_of_a_64_bit_range_is_refused.c
void set_four(unsigned char *chunk) { chunk[0] = 1; }
void write(unsigned char *bytes, unsigned long length, unsigned long index) {
    set_four(bytes + index);
}
```

```click
verifying "an_owned_window_past_the_end_of_a_64_bit_range_is_refused.c";
void set_four(uint8* chunk) {
    owns chunk[0..4];
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index) {
    requires index <= length;
    requires 3u64 <= length - index;
    owns bytes[0..length];
} by { execute(); simp(); }
```

```expect
fail: missing resource fact `owns bytes[index..(index + 4)]`
```
