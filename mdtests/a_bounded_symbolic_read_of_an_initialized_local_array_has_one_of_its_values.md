# A bounded symbolic read of an initialized local array has one of its values

Under `0 <= x && x < 4` the read `values[x]` splits into one case per
initialized cell, `x == 0` through `x == 3`. The case past them, `x != 0`
through `x != 3`, used to remain with an unknown value, so a claim about the
contents failed there. A bound the index is known not to equal now moves past
that value, so once `x != 0`, `x != 1` and `x != 2` hold, `x == 3` is decided
and the case past the cells is never formed.
`mdtests/a_bounded_symbolic_read_claimed_above_a_value_it_may_have_is_refused.md`
is the negative.

```c filename=a_bounded_symbolic_read_of_an_initialized_local_array_has_one_of_its_values.c
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
verifying "a_bounded_symbolic_read_of_an_initialized_local_array_has_one_of_its_values.c";

int32 f(int32 x) {
    ensures result >= 0;
    ensures result <= 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
