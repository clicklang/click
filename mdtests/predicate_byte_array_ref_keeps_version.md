# A declared byte-array predicate retains its version across a disjoint call

```c filename=byte-array-version.c
uint8 g[4];
uint8 h[4];

void touch_g() { g[0] = 1; }

uint8 keep_h() {
    touch_g();
    return h[0];
}
```

```click
verifying "byte-array-version.c";

predicate first_is(a: uint8[], value: uint8) {
    a[0] == value
}

void touch_g() {
    owns g[0..1];
}

uint8 keep_h() {
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
