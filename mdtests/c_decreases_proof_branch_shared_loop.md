# Proof branches share the same C loop identity

Both proof branches annotate the same source loop. The inactive branch uses a
same `n - i` measure as the active branch. Proof annotation order must
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
            decreases n - i;
            invariant i == 0;
            invariant n < 0;
        }
        execute();
        simp();
    } else {
        have n >= 0;
        loop {
            decreases n - i;
            invariant 0 <= i and i <= n;
            initialize by simp;
            preserve by { step(); close_invariants(); }
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
