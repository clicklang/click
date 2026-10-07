# a natural `goto` cycle's returned value is certified

The positive twin of
[`a_natural_goto_cycle_return_exit_is_a_function_exit.md`](a_natural_goto_cycle_return_exit_is_a_function_exit.md):
the exit branch returns `flag + 1` where `flag == 0`, and `ensures result ==
1` holds only on a certified return path that knows the branch condition. A
vacuous rule would also pass `ensures result == 0`, which the negative twin
rules out.

```c filename=a_natural_goto_cycle_return_value_is_certified.c
int32 stop_with_one(int32 flag) {
again:
    if (flag == 0) {
        return flag + 1;
    }
    flag = 0;
    goto again;
}
```

```click
verifying "a_natural_goto_cycle_return_value_is_certified.c";

int32 stop_with_one(int32 flag) {
    requires flag >= 0;
    ensures result == 1;
} by {
    loop {
        invariant flag >= 0;
        decreases flag;
    }
    simp();
}
```

```expect
pass
```
