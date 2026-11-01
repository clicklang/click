# An automatically closed loop splits at each of its C `if`s

The body has two C `if`s in a row and then the increment. Each `if` stores
to `found` when its guard holds and does nothing otherwise. With no written
`preserve` proof, the loop closer splits at each `if` as a function's implicit
tail does, so the increment runs on four paths, and each closes the
invariant, which no arm's store touches.

```c filename=an_automatically_closed_loop_splits_at_its_c_branches.c
int32 scan(int32* a, int32 n) {
    int32 i;
    int32 found;
    i = 0;
    found = 0;
    while (i < n) {
        if (a[0] == 7) {
            found = 1;
        }
        if (a[1] == 7) {
            found = 2;
        }
        i = i + 1;
    }
    return 0;
}
```

```click
verifying "an_automatically_closed_loop_splits_at_its_c_branches.c";

int32 scan(int32* a, int32 n) {
    views a[0..2];
    requires 0 <= n;
    requires n <= 3;
    ensures result == 0;
} by {
    step();
    step();
    step();
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
    }
    step();
    solve();
}
```

```expect
pass
```
