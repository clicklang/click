# `step_until(function.exit)` refuses an undecided branch

`step_until` never splits. When the C reaches an `if` the facts do not
decide, it is refused there and names the split to write: a proof `if` in
front of the C, or `branch` when the arms rejoin.

```c filename=step_until_function_exit_refuses_an_undecided_branch.c
int32 clamp(int32 x) {
    if (x > 10) {
        return 10;
    }
    return x;
}
```

```click
verifying "step_until_function_exit_refuses_an_undecided_branch.c";

int32 clamp(int32 x) {
    ensures result <= 10;
} by {
    step_until(function.exit);
}
```

```expect
fail: `step_until(function.exit)` stopped at a C branch the facts do not decide; it never splits. Split there with a proof `if <condition> { ... } else { ... }` (`click docs if`), or `branch` when the arms rejoin (`click docs branch`), and step each arm
```
