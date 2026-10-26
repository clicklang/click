# A proof `if` before the C decides the C branch in each arm

A proof `if` over the inputs, placed before the C, gives each arm its
condition. In each arm `step_until(function.exit)` reaches the C `if` and
decides `a > b` from the arm's condition, `b < a` or its negation, by exact
lookup or by the kernel's condition decision, without searching the proof
context, so neither arm splits and each arm states its path's result.

```c filename=pick_decided.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_decided.c";

int32 pick(int32 a, int32 b) {
    ensures result >= a;
} by {
    if b < a {
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
