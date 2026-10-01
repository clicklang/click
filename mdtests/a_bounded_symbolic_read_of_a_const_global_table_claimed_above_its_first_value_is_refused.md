# A bounded symbolic read of a const global table claimed above its first value is refused

The negative of
`mdtests/a_bounded_symbolic_read_of_a_const_global_table_has_one_of_its_values.md`:
the case that reads the first element has the value `1`.

```c filename=a_bounded_symbolic_read_of_a_const_global_table_claimed_above_its_first_value_is_refused.c
const int32 values[4] = {1, 2, 3, 4};

int32 g(int32 x) {
    int32 r = 0;
    if (0 <= x && x < 4) {
        r = values[x];
    }
    return r;
}
```

```click
verifying "a_bounded_symbolic_read_of_a_const_global_table_claimed_above_its_first_value_is_refused.c";

int32 g(int32 x) {
    ensures result >= 2;
} by {
    execute();
    simp();
}
```

```expect
fail: result >= 2; left side evaluated to 1
```
