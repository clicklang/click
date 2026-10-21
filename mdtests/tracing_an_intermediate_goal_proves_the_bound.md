# An intermediate goal proves the bound

The refused goal of `tracing_a_nonlinear_bound_is_the_refused_goal.md` is
`inner <= 2147483646` before `return inner + 1;`. Its argument is a chain:
`inner == w * h` after the call, `w * h <= 1000000` from the bounds, so the
addition is defined. Stepping to the `return` and writing the missing link as
a `have` lets the remaining execution prove the rest. This is the worked
example in `docs/concepts/tracing.md`.

```c filename=frame.c
int area(int w, int h) { return w * h; }
int frame(int w, int h) {
    int inner = area(w, h);
    return inner + 1;
}
```

```click
verifying "frame.c";

int32 area(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures result == w * h;
}

int32 frame(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures result == w * h + 1 by {
        step(); step();
        have w * h <= 1000000 by auto();
        execute();
    }
}
```

```expect
pass
```
