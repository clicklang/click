# An unsigned index below a signed bound is refused

The mixed-signedness negative beside
`mdtests/an_unsigned_index_below_a_variable_bound_indexes_an_array.md`.
`x < n` converts the `int32` `n` to `uint32`, while `n <= 4` is a signed
bound, and a negative `n` is a huge unsigned one. The unsigned test and the
signed bound are orders on different atoms (`n ^ 2^31` and `n`), and an
order chain does not compose across them, so the store is refused as
outside `values[0..4]`.

```c filename=an_unsigned_index_below_a_signed_bound_is_refused.c
void store_signed_bound(int32* values, uint32 x, int32 n) {
    if (x < n) {
        values[x] = 0;
    }
}
```

```click
verifying "an_unsigned_index_below_a_signed_bound_is_refused.c";

void store_signed_bound(int32* values, uint32 x, int32 n) {
    requires n <= 4;
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns values[x..(x + 1)]`
```
