# A symbolic read one past a global array is refused for its bound

The global counterpart of
`mdtests/a_symbolic_read_one_past_an_initialized_local_array_is_refused.md`.
The C frontend checks a global array's index with a lowered `assert`; the
refusal names that check's condition and the facts it consulted rather than
the bare `0 = 1` its false path leaves.

```c filename=a_symbolic_read_one_past_a_global_array_is_refused.c
int32 values[4];

int32 global_past(int32 x) {
    int32 r;
    r = 1;
    if (0 <= x && x < 5) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_symbolic_read_one_past_a_global_array_is_refused.c";

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
