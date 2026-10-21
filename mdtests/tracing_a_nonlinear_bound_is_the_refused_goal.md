# A nonlinear bound is the refused goal

`frame` adds one to a product its callee returns. The implicit `auto` cannot
show that the addition does not overflow: it needs `w * h <= 1000000`, a
nonlinear consequence of the bounds, which it does not derive. The refusal's
goal is the addition's definedness condition at the `return` statement,
`inner <= 2147483646`; the companion
`tracing_an_intermediate_goal_proves_the_bound.md` proves it. This is the
worked example in `docs/concepts/tracing.md`.

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
    ensures result == w * h + 1;
}
```

```expect
fail: `execute()` produced undefined behavior: signed overflow
```
