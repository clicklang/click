# `loop` proves a natural `goto` cycle with multiple exits

Multiple conditions may leave the cycle at the same final label. The existing
`loop` proof still supplies the invariant and termination evidence.

```c filename=natural_goto_multiple_exit_labels.c
int32 count_down_or_stop(int32 n) {
again:
    if (n == 0)
        goto done;
    if (n == 1)
        goto done;
    n--;
    goto again;
done:
    return n;
}
```

```click
verifying "natural_goto_multiple_exit_labels.c";

int32 count_down_or_stop(int32 n) {
    requires n >= 0;
    ensures result == 0 or result == 1;
} by {
    loop {
        invariant n >= 0;
        decreases n;
        maintain by {
            if n == 0 {
                step();
                have n == 0 or n == 1 by known();
                step();
            } else {
                step();
                step();
                if n == 1 {
                    step();
                    have n == 0 or n == 1 by known();
                    step();
                } else {
                    step();
                    step();
                    step();
                }
            }
        }
    }
}
```

```expect
pass
```
