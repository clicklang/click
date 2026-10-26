# A proof if uses facts proved earlier in source order

A `have` before a proof `if` is a fact in both arms. Here the `else` arm, where
`a <= b`, steps to exit, where `result >= a` follows from `result == b` and
the earlier `have old(a) >= old(b);`.

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
    have old(a) >= old(b);
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
pass
```
