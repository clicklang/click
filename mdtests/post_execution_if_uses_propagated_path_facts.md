# A post-execution if uses exactly propagated path facts

The false arm of the proof split refutes `a > b` in the required
`a > b or a == b`, so exact propagation supplies `a == b` before execution.
The post-execution condition is then decided from the path's existing facts;
its nested `have` is not used early.

```c filename=pick.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
    ensures result >= a;
} by {
    if a > b {
        step_until(function.exit);
        if old(a) >= old(b) {
            have old(a) >= old(b);
            have result == a;
        } else {
            have result == b;
        }
    } else {
        step_until(function.exit);
        if old(a) >= old(b) {
            have old(a) >= old(b);
            have result == a;
        } else {
            have result == b;
        }
    }
}
```

```expect
pass
```
