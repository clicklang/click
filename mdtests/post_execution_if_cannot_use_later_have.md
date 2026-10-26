# A post-execution if cannot use a fact from its own arm

A proof `if` on the inputs decides the C `if`, so each of its arms steps to
function exit with `step_until(function.exit)`. There, a proof `if` on
`old(a) >= old(b)` must be decided by the path's facts; the `have` inside its
own arm cannot decide it.

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
fail: focused outcome does not decide the post-execution `if` condition: `old(a) >= old(b)`
```
