# Proof branches share the same C loop identity

Both proof branches annotate the same source loop. The inactive branch uses `0`; the active branch uses `n - i`. Each
branch owns its own ranking proof. Proof annotation order must
not create a fictitious second C loop in the termination plan.

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
    ensures result >= 0;
} by {
    step();
    step();
    if n < 0 {
        loop {
            decreases 0;
            invariant i == 0;
            invariant n < 0;
        }
        step_until(function.exit);
        close();
    } else {
        have n >= 0;
        loop {
            decreases n - i;
            invariant 0 <= i and i <= n;
            initialize by close();
            maintain by { step(); }
        }
        step_until(function.exit);
        close();
    }
}
```

```expect
pass
```
