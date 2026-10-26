# A proof case split before the C forks the paths it does not decide

The C returns `a` when `a > 0` and `0` otherwise. The proof splits on
`a == 5` before the C runs. In the `a == 5` arm that decides the C `if`, so
the arm has one path and steps to exit with `step_until(function.exit)`
before closing the postcondition. In the other arm the facts do not decide
`a > 0`, so the arm's implicit tail forks there into one path per polarity,
records the case on each, and closes the postcondition on each path.

```c filename=clamp_positive.c
int32 clamp_positive(int32 a) {
    if (a > 0) {
        return a;
    }
    return 0;
}
```

```click
verifying "clamp_positive.c";

int32 clamp_positive(int32 a) {
    ensures result >= 0;
} by {
    if a == 5 {
        step_until(function.exit);
        solve();
    } else {}
}
```

```expect
pass
```
