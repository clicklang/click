# `step_until` steps to function exit

`step_until(function.exit)` repeats `step()` until the function returns, and
the proof continues at exit, where `result` names the returned value. It
never splits: a C `if` the facts decide is stepped through, and an
undecided one needs a proof `if` in front of it, each arm stepping to exit
on its own path.

```c filename=step_until_steps_to_function_exit.c
int32 add_one(int32 x) {
    int32 y = x + 1;
    if (y > 0) {
        return y;
    }
    return 0;
}

int32 clamp(int32 x) {
    if (x > 10) {
        return 10;
    }
    return x;
}
```

```click
verifying "step_until_steps_to_function_exit.c";

int32 add_one(int32 x) {
    requires 0 <= x;
    requires x < 100;
    ensures result == x + 1;
} by {
    step_until(function.exit);
    have result == x + 1;
}

int32 clamp(int32 x) {
    ensures result <= 10;
} by {
    if x > 10 {
        step_until(function.exit);
        have result == 10;
    } else {
        step_until(function.exit);
        have result == x;
    }
}
```

```expect
pass
```
