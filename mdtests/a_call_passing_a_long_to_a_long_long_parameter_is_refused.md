# A call passing a `long` to a `long long *` parameter is refused

Click verifies each function separately, and a callee is verified
accessing what its pointer parameter points to through the parameter's
pointee type. A caller that passes a declared `long`, hidden behind a
`void *`, to a `long long *` parameter is refused at the call
(`design/effective-types.md`), while the same call with a `long *`
parameter verifies.

```c filename=calls.c
long long read_ll(long long *q) { return *q; }
long read_l(long *q) { return *q; }

long long caller(void) {
    long value = 7;
    void *v = &value;
    return read_ll(v);
}

long caller_ok(void) {
    long value = 7;
    return read_l(&value);
}
```

```click
verifying "calls.c";

long long read_ll(long long *q) {
    views q[0..1];
    ensures result == q[0];
} by {
    execute();
    simp();
}

long read_l(long *q) {
    views q[0..1];
    ensures result == q[0];
} by {
    execute();
    simp();
}

long long caller() {
    ensures true;
} by {
    execute();
}
```

```expect
fail: call to `read_ll` passes an object of type `long` to parameter `q`, which points to `long long`
```
