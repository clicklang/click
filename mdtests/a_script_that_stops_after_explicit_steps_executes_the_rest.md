# A script that stops after explicit steps executes the rest

A script that stops at a live frontier ends with the implicit tail: it
executes whatever C remains and then closes every open goal, as an omitted
proof does. A `have` before the end is part of the explicit prefix, not a
shape the drivers decline: this is the worked example of
`docs/concepts/tracing.md` stopping before the `return` instead of ending in
`execute();`.

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
    ensures to_integer(result) == to_integer(w * h);
}

int32 frame(int32 w, int32 h) {
    requires w >= 0 and w <= 1000;
    requires h >= 0 and h <= 1000;
    ensures to_integer(result) == to_integer(w * h + 1) by {
        step(); step();
        have to_integer(w * h) <= 1000000;
    }
}
```

```expect
pass
```
