# a loop measure proves termination

```c filename=c_decreases_loop.c
int32 drain(int32 n) {
    while (n > 0) {
        n = n - 1;
    }
    return n;
}
```

```click
verifying "c_decreases_loop.c";

int32 drain(int32 n) {
    requires n >= 0;
    ensures result == 0;
} by {
    loop {
        decreases n;
        invariant n >= 0;
        initialize by solve();
        preserve by {
            have 0 <= to_integer(n - 1);
            step();
            close_invariants() by {
                both { solve() using { 0 <= n; }; }
                and {
                    both { solve() using { 0 <= n; }; }
                    and { solve() using { 0 <= n; }; }
                }
            }
        }
    }
    step();
    solve();
}
```

```expect
pass
```
