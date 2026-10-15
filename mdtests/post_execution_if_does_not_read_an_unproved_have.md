# A post-execution `if` does not pick an arm on an unproved `have`

Without the `requires`, `old(a) >= old(b)` is false on the path that returns
`b` when `a < b`. The `have` stating it is refused where it is written, so the
`if` after it never selects an arm on it.

```c filename=pick_unproved_have.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_unproved_have.c";

int32 pick(int32 a, int32 b) {
    ensures result >= a;
} by {
    execute();
    have old(a) >= old(b);
    if old(a) >= old(b) {
        have result == a;
    } else {
        have result == b;
    }
}
```

```expect
fail: could not establish `old(a) >= old(b)`
```
