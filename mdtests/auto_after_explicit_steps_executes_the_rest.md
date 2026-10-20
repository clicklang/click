# `auto` after explicit steps executes the rest

Written after explicit steps at a live frontier, `auto();` executes whatever C
remains and then closes every open goal, as the `auto` an omitted proof
stands for does. A `have` before it is part of the explicit prefix, not a
shape the drivers decline: this is the worked example of
`docs/concepts/tracing.md` ending in `auto();` rather than `execute();`.

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
        auto();
    }
}
```

```expect
pass
```
