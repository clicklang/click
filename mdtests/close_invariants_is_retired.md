# `close_invariants` is retired

A `preserve` script closes the loop's invariants and its `decreases` when it
reaches the back edge, as a function proof closes its `ensures` when it
reaches the exit: each by `solve()`, which reads the facts the script has
stated. A member that needs help is proved with `have <invariant> by { ... }`
before the back edge. The tactic that used to name that closing step is
refused with the replacement.

```c filename=close_invariants_is_retired.c
int32 count(int32 n) {
    int32 i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "close_invariants_is_retired.c";

int32 count(int32 n) {
    requires n >= 0;
    ensures result == n;
} by {
    step();
    loop {
        decreases n - i;
        invariant 0 <= i and i <= n;
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    solve();
}
```

```expect
fail: `close_invariants` is retired
```
