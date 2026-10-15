# A post-execution `if` reads a `have` written before it

On the path where `a > b` is false, `old(a) >= old(b)` follows from the
`requires` only by a case split. The `have` before the `if` states it, and is
checked where it is written, before the arm the `if` selects runs anything, so
the `if` reads it to pick that arm.

```c filename=pick_after_have.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_after_have.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
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
pass
```
