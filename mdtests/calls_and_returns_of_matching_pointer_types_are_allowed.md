# Calls and returns of matching pointer types are allowed

A call passing a declared `long` to a `long *` parameter, and a function
returning its `struct a *` parameter through a `void *`, keep each object's
type and verify.

```c filename=calls.c
struct a { int x; };
long read_l(long *q) { return *q; }

long caller_ok(void) {
    long value = 7;
    return read_l(&value);
}

struct a *same(struct a *pa) {
    void *v = pa;
    return v;
}
```

```click
verifying "calls.c";

long read_l(long *q) {
    views q[0..1];
    ensures result == q[0];
} by {
    execute();
    simp();
}

long caller_ok() {
    ensures result == 7;
} by {
    execute();
    simp();
}

struct a *same(struct a *pa) {
    ensures address(result) == address(pa);
} by {
    execute();
    normalize();
}
```

```expect
pass
```
