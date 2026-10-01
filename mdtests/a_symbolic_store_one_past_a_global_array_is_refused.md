# A symbolic store one past a global array is refused for its bound

The store counterpart of
`mdtests/a_symbolic_read_one_past_a_global_array_is_refused.md`.

```c filename=a_symbolic_store_one_past_a_global_array_is_refused.c
int32 values[4];

int32 global_past(int32 x) {
    int32 r;
    r = 1;
    if (0 <= x && x < 5) {
        values[x] = 3;
    }
    return r;
}
```

```click
verifying "a_symbolic_store_one_past_a_global_array_is_refused.c";

int32 global_past(int32 x) {
    owns values[0..4];
    ensures result == result;
} by {
    execute();
    simp();
}
```

```expect
fail: missing prerequisite (array subobject index must be at least 0 and less than 4): could not show `x >= 0 && x < 4`
```
