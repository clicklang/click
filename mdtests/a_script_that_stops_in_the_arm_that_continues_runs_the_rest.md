# A script that stops in the arm that continues runs the rest

When one arm of a `branch` returns, the rest of the script runs in the arm
that continues. A script that stops there, with C still to run, is
finished by the implicit tail, as any other script is: it runs the C that
is left and closes each goal. The script may stop right after the
`branch`, or after more work in the continuing arm.

```c filename=a_script_that_stops_in_the_arm_that_continues_runs_the_rest.c
int32 clamp(int32 x) {
    if (x > 10) {
        return 10;
    }
    return x;
}

int32 clamp_again(int32 x) {
    if (x > 10) {
        return 10;
    }
    return x;
}
```

```click
verifying "a_script_that_stops_in_the_arm_that_continues_runs_the_rest.c";

int32 clamp(int32 x) {
    ensures result <= 10;
} by {
    branch {
        step();
        solve();
    } else {}
}

int32 clamp_again(int32 x) {
    ensures result <= 10;
} by {
    branch {
        step();
        solve();
    } else {}
    have x <= 10;
}
```

```expect
pass
```
