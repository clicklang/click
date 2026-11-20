# Active proof branches own distinct loop measures

Both branches execute and rank the same C loop using different measures.

```c filename=proof_branch_shared_loop.c
int32 count_to_bound(int32 n) {
    int32 i;
    i = 0;
    while (i < n) {
        i++;
    }
    return i;
}
```

```click
verifying "proof_branch_shared_loop.c";

int32 count_to_bound(int32 n) {
    requires 0 <= n and n <= 100;
    ensures result >= 0;
} by {
    step();
    step();
    if n < 50 {
        loop {
            decreases n - i;
            invariant 0 <= i and i <= n;
            initialize by solve();
            maintain by { step(); }
        }
        step_until(function.exit);
        solve();
    } else {
        loop {
            decreases n - i + 1;
            invariant 0 <= i and i <= n;
            initialize by solve();
            maintain by { step(); }
        }
        step_until(function.exit);
        solve();
    }
}
```

```expect
pass
```
