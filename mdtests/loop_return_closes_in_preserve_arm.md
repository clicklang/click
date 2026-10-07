# A loop return closes in its preservation arm

The returning arm owns its `result == 7` proof. The tail applies only to the
normal exit, where `result == 5`. Neither list may be silently dropped.

```c filename=loop_return_closes_in_preserve_arm.c
int32 f(int32 n) {
    int32 i = 0;
    while (i < n) {
        if (i == 2) {
            return 7;
        }
        i = i + 1;
    }
    return i;
}
```

```click
verifying "loop_return_closes_in_preserve_arm.c";

int32 f(int32 n) {
    requires n == 5;
    ensures result == 5 or result == 7;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;
        preserve by {
            if i == 2 {
                step();
                step();
                have result == 7 by simp;
                simp();
            } else {
                step();
                step();
                step();
            }
        }
    }
    step();
    have result == 5 by simp;
    simp();
}
```

```expect
pass
```
