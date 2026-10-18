# `cases` after execution takes the arm a decided disjunct selects

On an outcome path whose facts decide a disjunct, `cases` after execution runs only that arm, as a proof `if` runs only the arm its decided condition selects. Here `x == 1` holds, so only the first arm runs and the path does not fork; the second arm is never checked.

```c filename=cases_after_execution_takes_the_decided_arm.c
int32 f(int32 x) {
    return x;
}
```

```click
verifying "cases_after_execution_takes_the_decided_arm.c";

int32 f(int32 x) {
    requires x == 1;
    ensures result == 1;
} by {
    execute();
    cases {
        x == 1 => { simp(); }
        x == 2 => { simp(); }
    }
}
```

```expect
pass
```
