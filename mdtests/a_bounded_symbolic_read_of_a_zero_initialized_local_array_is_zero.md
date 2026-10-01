# A bounded symbolic read of a zero-initialized local array is zero

`= {0}` stores the array as one constant run of zeros. A read at an index
the facts place on the run's live slots is that constant: no element was
stored over the run, so every element it may name holds `0`.
`mdtests/a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_not_one.md`
is the negative.

```c filename=a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_zero.c
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
verifying "a_bounded_symbolic_read_of_a_zero_initialized_local_array_is_zero.c";

int32 f(int32 x) {
    ensures result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
