# A declared predicate keeps the array version after a write

```c filename=post-write-array.c
void touch(int32* p) { *p = 1; }

int32 keep(int32 a[]) {
    a[0] = 7;
    int32 local = 0;
    touch(&local);
    local = 2;
    return a[0];
}
```

```click
verifying "post-write-array.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

void touch(int32* p) {
    owns *p;
}

int32 keep(int32 a[]) {
    owns a[0..1];
    ensures result == 7;
} by {
    step();
    have first_is(a, 7) by { unfold(first_is(a, 7)); close(); }
    step();
    step();
    step();
    have first_is(a, 7) by { close(); }
    step_until(function.exit);
    close();
}
```

```expect
pass
```
