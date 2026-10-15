# A post-execution `if` refuses a condition a path does not decide

On the path where `a > b` is false, `old(a) >= old(b)` follows from the
`requires` only by a case split, which the `if` does not search for. The refusal
identifies the `if`, its condition, and the undecided outcome path. Proving the
condition with an earlier `have` allows the `if` to select its arm.

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
    execute();
    if old(a) >= old(b) {
        have result == a;
    } else {
        have result == b;
    }
}
```

```expect
fail: post-execution path 1: `pick.contract` proof step tactic 1: focused outcome does not decide the post-execution `if` condition: `old(a) >= old(b)`
```
