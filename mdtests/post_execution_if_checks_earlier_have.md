# A failed have before a post-execution if is still checked

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
    execute();
    have old(a) < old(b);
    if old(a) >= old(b) {
        have result == a;
    } else {
        have result == b;
    }
}
```

```expect
fail: `pick.contract` proof step tactic 1 > have body tactic 1: `simp` failed for `pick.contract`: could not establish `old(a) < old(b)`
```
