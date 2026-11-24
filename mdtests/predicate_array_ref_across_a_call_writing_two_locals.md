# A declared predicate retains its array version across a call that writes two locals

```c filename=keep-multiple-locals.c
void touch(int32* p, int32* q) {
    *p = 1;
    *q = 2;
}

int32 keep(int32 a[]) {
    int32 left = 0;
    int32 right = 0;
    touch(&left, &right);
    return a[0];
}
```

```click
verifying "keep-multiple-locals.c";

predicate first_is(a: int32[], value: int32) {
    a[0] == value
}

void touch(int32* p, int32* q) {
    owns *p;
    owns *q;
}

int32 keep(int32 a[]) {
    views a[0..1];
    requires first_is(a, 7);
    ensures result == 7;
} by {
    step_until(call(0).entry);
    step();
    have first_is(a, 7) by { close(); }
    unfold(first_is(a, 7));
    step_until(function.exit);
    close();
}
```

```expect
pass
```
