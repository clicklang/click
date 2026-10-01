# An unguarded narrow unsigned index into a global array is refused

The type range of a `uint8` index is `0..255`. It supplies the lower half
of the subscript check `x >= 0 && x < 4` and nothing more: with no source
test bounding `x` above, the access is refused.

```c filename=an_unguarded_narrow_unsigned_index_into_a_global_array_is_refused.c
int32 values[4];

int32 read_byte(uint8 x) {
    return values[x];
}
```

```click
verifying "an_unguarded_narrow_unsigned_index_into_a_global_array_is_refused.c";

int32 read_byte(uint8 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: could not show `x >= 0 && x < 4`
```
