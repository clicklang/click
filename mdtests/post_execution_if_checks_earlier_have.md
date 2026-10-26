# A failed have before a proof if is still checked

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
    have old(a) < old(b);
    if old(a) > old(b) {
        step_until(function.exit);
        have result == a;
    } else {
        step_until(function.exit);
        have result == b;
    }
}
```

```expect
fail: `solve` failed for `pick.contract`: could not establish `old(a) < old(b)`
```
