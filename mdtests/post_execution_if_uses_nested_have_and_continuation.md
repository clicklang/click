# Nested proof-if arms and their continuation see earlier facts

A proof `if` before the C splits on `a > b`, and each arm steps to exit with
`step_until(function.exit)`. In the first arm a `have` precedes a nested proof
`if` at exit; both nested arms and the continuation after them see it.

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
    if old(a) > old(b) {
        step_until(function.exit);
        have old(a) >= old(b);
        if old(a) >= old(b) {
            have result == a;
        } else {
            have result == b;
        }
        if old(a) >= old(b) {
            have result >= a;
        } else {
            have result == b;
        }
    } else {
        step_until(function.exit);
        have old(a) >= old(b);
        have result == b;
    }
}
```

```expect
pass
```
