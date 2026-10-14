# a counter loop names its initialize and preserve obligations

This checks the full induction syntax for a counter loop: `initialize by auto`
proves the invariants at loop entry, and `preserve` executes one iteration and
reestablishes them before the implicit invariant closer.

```c filename=count_to_loop_initialize_by_auto_and_preserve.c
int32 count_to(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count_to_loop_initialize_by_auto_and_preserve.c";

int32 count_to(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;

        initialize by auto;
        preserve by {
            step();
            simp();
        }
    }
    step();
    simp();
}
```

```expect
pass
```
