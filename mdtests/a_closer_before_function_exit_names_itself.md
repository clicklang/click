# A closer before function exit names itself

`normalize()` closes the outcome claims at function exit, but this script
writes it while the frontier is still at the `return`. The refusal names
`normalize` and where the frontier stands. It used to say that no driver
supports the script's shape and blame the earlier `have`, which is a
valid step at that point.

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
        normalize();
    }
}
```

```expect
fail: `normalize` works on the outcome claims at function exit and does not execute
```
