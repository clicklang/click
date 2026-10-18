# The arms of `cases` that do not rejoin are refused

When tactics follow `cases`, its live arms must end at the same program point in the same state. Here one arm steps a statement and the other does not, so what follows would have two states to check from, and the `cases` is refused rather than running `execute()` once per arm.

```c filename=cases_arms_that_do_not_rejoin_are_refused.c
int32 f(int32 x) {
    if (x > 0) {
        return 1;
    }
    return 0;
}
```

```click
verifying "cases_arms_that_do_not_rejoin_are_refused.c";

int32 f(int32 x) {
    requires x == 1 or x == 2;
    ensures result == 1;
} by {
    cases {
        x == 1 => { step(); }
        x == 2 => { }
    }
    execute();
}
```

```expect
fail: the arms of this `cases` do not rejoin
```
