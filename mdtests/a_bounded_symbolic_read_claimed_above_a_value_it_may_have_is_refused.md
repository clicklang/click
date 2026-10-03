# A bounded symbolic read claimed above a value it may have is refused

The negative of
`mdtests/a_bounded_symbolic_read_of_an_initialized_local_array_has_one_of_its_values.md`:
in the case `x == 0` the read is `1`, so `result >= 2` is refused there.

```c filename=a_bounded_symbolic_read_claimed_above_a_value_it_may_have_is_refused.c
int32 f(int32 x) {
    int32 values[4] = {1, 2, 3, 4};
    int32 r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_claimed_above_a_value_it_may_have_is_refused.c";

int32 f(int32 x) {
    ensures result >= 2;
} by {
    execute();
    simp();
}
```

```expect
fail: result >= 2; left side evaluated to 1
```
