# A wide unsigned index at its bound is refused

`mdtests/an_unsigned_index_at_its_bound_is_refused.md` with a `uint64`
index. `x <= 4u` still admits the one-past element `values[4]`, which the
owned range `values[0..4]` does not hold, so the write at `values[x]` is
refused.

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
fail: missing resource fact `owns values[x..(x + 1)]`
```
