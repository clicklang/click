# A bounded symbolic read of a zero-initialized local array is not one

The negative of
`mdtests/a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_zero.md`.

```c filename=a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_not_one.c
int32 f(int32 x) {
    int32 values[4] = {0};
    int32 r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_not_one.c";

int32 f(int32 x) {
    ensures result == 1;
} by {
    execute();
    simp();
}
```

```expect
fail: result == 1; left side evaluated to 0
```
