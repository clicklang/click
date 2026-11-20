# A declared predicate retains its array version across a local call

```c filename=keep-predicate.c
void touch(int32* p) { *p = 1; }

int32 keep(int32 a[]) {
    int32 local = 0;
    touch(&local);
    local = 2;
    return a[0];
}
```

```click
verifying "keep-predicate.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

void touch(int32* p) {
    owns *p;
}

int32 keep(int32 a[]) {
    views a[0..1];
    requires first_is(a, 7);
    ensures result == 7;
} by {
    step();
    step();
    step();
    step();
    have first_is(a, 7) by { known(); }
    unfold(first_is(a, 7));
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
