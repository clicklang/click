# An unsigned index at its bound is refused

The negative beside
`mdtests/an_unsigned_index_below_a_constant_bound_indexes_a_parameter_array.md`.
`x <= 4u` files `0 <= x` and `x <= 4`, which admit `x == 4`: the store
`values[4]` is one past `values[0..4]`, so the owned range does not cover
it.

```c filename=an_unsigned_index_at_its_bound_is_refused.c
void write_at_bound(int32* values, uint32 x) {
    if (x <= 4u) {
        values[x] = 7;
    }
}
```

```click
verifying "an_unsigned_index_at_its_bound_is_refused.c";

void write_at_bound(int32* values, uint32 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: missing resource fact `owns values[x..(x + 1)]`
```
