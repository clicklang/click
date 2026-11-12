# Each returned outcome proves its own theorem premises

```c filename=outcome_apply.c
int choose_positive(int x) { if (x > 0) { return x; } else { return 1; } }
int increment_result(int x) { return x + 1; }
```

```click
verifying "outcome_apply.c";
theorem nonnegative(value: int32) {
    requires value >= 0;
    ensures value >= 0 by assumption();
}
int32 choose_positive(int32 x) {
    ensures result >= 0 by {
        branch {
            step_until(function.exit);
            apply(nonnegative(result));
            assumption();
        } else {
            step_until(function.exit);
            apply(nonnegative(result));
            assumption();
        }
    }
}
theorem increased(before: int32, after: int32) {
    requires after > before;
    ensures after > before by assumption();
}
int32 increment_result(int32 x) {
    requires 0 <= x;
    requires x < 10;
    ensures result > old(x) by {
        step();
        apply(increased(old(x), result));
        assumption();
    }
}
```

```expect
pass
```
