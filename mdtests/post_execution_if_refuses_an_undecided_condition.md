# A proof `if` arm refuses to step past a C branch it does not decide

On the arm where `a >= b` holds, the C condition `a > b` is still open: it
holds when `a > b` and fails when `a == b`. `step_until(function.exit)` never
splits, so it stops at the C `if` and is refused, naming the C condition and
its two feasible paths. Splitting on the C condition itself, with a proof
`if a > b` or a `branch` at the C `if`, lets each arm step to exit.

```c filename=pick_undecided.c
int32 pick(int32 a, int32 b) {
    if (a > b) {
        return a;
    }
    return b;
}
```

```click
verifying "pick_undecided.c";

int32 pick(int32 a, int32 b) {
    requires a > b or a == b;
    ensures result >= a;
} by {
    if a >= b {
        step_until(function.exit);
        have result == a;
    } else {
        step_until(function.exit);
        have result == b;
    }
}
```

```expect
fail: `pick.contract` tactic 1: `step` could not prove that the next C `if` condition `(a > b)` is one exact truth value
```
