# A narrow unsigned index one past a global array is refused

The negative beside
`mdtests/a_narrow_unsigned_index_below_a_constant_bound_indexes_a_global_array.md`.
The `uint8` range gives `0 <= x`, and `x < 5` admits `x == 4`, so the C
frontend's subscript check `x >= 0 && x < 4` does not hold.

```c filename=a_narrow_unsigned_index_one_past_a_global_array_is_refused.c
int32 values[4];

void write_byte(uint8 x) {
    if (x < 5) {
        values[x] = 7;
    }
}
```

```click
verifying "a_narrow_unsigned_index_one_past_a_global_array_is_refused.c";

void write_byte(uint8 x) {
    owns values[0..4];
} by {
    execute();
    simp();
}
```

```expect
fail: could not show `x >= 0 && x < 4`
```
