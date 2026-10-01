# A wide unsigned index at its bound is refused

`mdtests/an_unsigned_index_at_its_bound_is_refused.md` with a `uint64`
index. `x <= 4u` files `0 <= x` and `x <= 4` on the index's low word, which
still admit the one-past element `values[4]`.

```c filename=a_wide_unsigned_index_at_its_bound_is_refused.c
void write_at_bound(int32* values, uint64 x) {
    if (x <= 4u) {
        values[x] = 7;
    }
}
```

```click
verifying "a_wide_unsigned_index_at_its_bound_is_refused.c";

void write_at_bound(int32* values, uint64 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: only when `0 <= truncate32(x)` and `(truncate32(x) + 1) <= 4`
```
