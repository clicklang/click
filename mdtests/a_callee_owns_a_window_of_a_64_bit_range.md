# A callee owns a window of a 64-bit range

`set_four(bytes + index)` hands the callee four owned bytes that start at a
`size_t` index of an owned range with a `size_t` bound, as
`a_callee_takes_a_window_of_a_64_bit_range.md` hands a viewed one. The
caller's `owns bytes[0..length]` is split around the window, and the window
the callee returns rejoins the two pieces, so the caller hands back the
whole range. `set_tail` takes the suffix `bytes[i..length]` at the same
base, which rejoins the prefix the same way. Nothing is cast and no bound on
`length` is stated.

`an_owned_window_past_the_end_of_a_64_bit_range_is_refused.md` leaves one
element out.

```c filename=a_callee_owns_a_window_of_a_64_bit_range.c
void set_four(unsigned char *chunk) { chunk[0] = 1; chunk[3] = 4; }
void write(unsigned char *bytes, unsigned long length, unsigned long index) {
    set_four(bytes + index);
}
void set_tail(unsigned char *bytes, unsigned long i, unsigned long length) { bytes[i] = 2; }
void tail(unsigned char *bytes, unsigned long i, unsigned long length) {
    set_tail(bytes, i, length);
}
```

```click
verifying "a_callee_owns_a_window_of_a_64_bit_range.c";
void set_four(uint8* chunk) {
    owns chunk[0..4];
    ensures chunk[0] == 1;
} by { execute(); simp(); }
void write(uint8* bytes, uint64 length, uint64 index) {
    requires index <= length;
    requires 4u64 <= length - index;
    owns bytes[0..length];
} by { execute(); simp(); }
void set_tail(uint8* bytes, uint64 i, uint64 length) {
    requires i < length;
    owns bytes[i..length];
} by { execute(); simp(); }
void tail(uint8* bytes, uint64 i, uint64 length) {
    requires i < length;
    owns bytes[0..length];
} by { execute(); simp(); }
```

```expect
pass
```
