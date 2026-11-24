# A declared predicate retains its automatic array through disjoint calls

```c filename=local-array-version.c
void touch(int32* p) { *p = 1; }

int32 keep_local() {
    int32 a[1];
    a[0] = 7;
    int32 other = 0;
    touch(&other);
    return a[0];
}
```

```click
verifying "local-array-version.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

void touch(int32* p) { owns *p; }

int32 keep_local() {
    ensures result == 7;
} by {
    step();
    step();
    have first_is(a, 7) by { unfold(first_is(a, 7)); close(); }
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
