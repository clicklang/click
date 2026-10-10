# An unsigned index below a wrapped bound is refused

The wrapping negative beside
`mdtests/an_unsigned_index_below_a_variable_bound_indexes_an_array.md`.
`n - 1u` wraps to `UINT32_MAX` when `n` is zero, so `n <= 4u32` does not
bound it: the flipped atom `(n - 1u) ^ 2^31` is not related to
`n ^ 2^31` by any order rule, and the store is refused as outside
`values[0..4]`.

```c filename=an_unsigned_index_below_a_wrapped_bound_is_refused.c
void store_wrapped(int32* values, uint32 x, uint32 n) {
    if (x < n - 1u) {
        values[x] = 0;
    }
}
```

```click
verifying "an_unsigned_index_below_a_wrapped_bound_is_refused.c";

void store_wrapped(int32* values, uint32 x, uint32 n) {
    requires n <= 4u32;
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns values[x]`
```
