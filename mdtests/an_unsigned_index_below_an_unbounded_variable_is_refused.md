# An unsigned index below an unbounded variable is refused

The negative beside
`mdtests/an_unsigned_index_below_a_variable_bound_indexes_an_array.md`.
Nothing bounds `n`, so `x < n` admits any `x`, and the store is refused as
outside `values[0..4]`.

```c filename=an_unsigned_index_below_an_unbounded_variable_is_refused.c
void store_unbounded(int32* values, uint32 x, uint32 n) {
    if (x < n) {
        values[x] = 0;
    }
}
```

```click
verifying "an_unsigned_index_below_an_unbounded_variable_is_refused.c";

void store_unbounded(int32* values, uint32 x, uint32 n) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns values[x..(x + 1)]`
```
