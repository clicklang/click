# A declared predicate retains a static array version across writes to another object

```c filename=static-array-version.c
int32 g[4];
int32 h[4];

void touch_g() { g[0] = 1; }

int32 keep_h() {
    touch_g();
    return h[0];
}
```

```click
verifying "static-array-version.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

void touch_g() {
    owns g[0..1];
}

int32 keep_h() {
    owns g[0..1];
    views h[0..1];
    requires first_is(h, 7);
    ensures result == 7;
} by {
    step();
    have first_is(h, 7) by { close(); }
    unfold(first_is(h, 7));
    step_until(function.exit);
    close();
}
```

```expect
pass
```
