# A declared predicate retains its static array at a branch join

```c filename=join-array-version.c
int32 h[4];

int32 keep_h(int32 flag) {
    int32 local;
    if (flag >= 0) {
        local = 1;
    } else {
        local = 2;
    }
    return h[0];
}
```

```click
verifying "join-array-version.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

int32 keep_h(int32 flag) {
    views h[0..1];
    requires first_is(h, 7);
    ensures result == 7;
} by {
    step();
    have first_is(h, 7) by { known(); }
    branch ensuring {
        fact local >= 0;
    } {
        true => { step(); }
        false => { step(); }
    }
    have first_is(h, 7) by { known(); }
    unfold(first_is(h, 7));
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
