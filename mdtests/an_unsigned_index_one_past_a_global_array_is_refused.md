# An unsigned index one past a global array is refused

The negative beside
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_global_array.md`.
`x < 5u` files `0 <= x` and `x < 5`, which admit `x == 4`, so the C
frontend's subscript check `x >= 0 && x < 4` does not hold.

```c filename=an_unsigned_index_one_past_a_global_array_is_refused.c
int32 values[4];

void write_global(uint32 x) {
    if (x < 5u) {
        values[x] = 7;
    }
}
```

```click
verifying "an_unsigned_index_one_past_a_global_array_is_refused.c";

void write_global(uint32 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: could not show `x >= 0 && x < 4`
```
