# An unranked sibling retains its termination obligation

The inactive path's checked constant measure cannot certify the infinite loop
on the other path. Both checked branch rules must survive proof-state joining.

```c filename=termination-branch-probe.c
int32 f(int32 n) {
    while (n > 0) {
        n = 1;
    }
    return 0;
}
```

```click
target "x86_64-linux-userspace";
verifying "termination-branch-probe.c";
int32 f(int32 n) diverges {
    ensures result == 0;
} by {
    if n <= 0 {
        loop {
            decreases 0;
            invariant n <= 0;
        }
        execute();
        simp();
    } else {
        have n > 0;
        have n >= 0 by { arithmetic() using { n > 0; } }
        loop {
            invariant n >= 0;
        }
        execute();
        simp();
    }
}
```

```expect
pass
```
