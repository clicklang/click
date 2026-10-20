# `auto` after explicit steps reports the remaining goal

Without the intermediate `have`, the `auto();` written after the call step
executes the `return` and is refused at its overflow, as the omitted proof
is. The refusal names that statement, not an unsupported proof shape.

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
        auto();
    }
}
```

```expect
fail: produced undefined behavior: signed overflow
```
