# An indexed store through a pointer of another rank is refused

A pointer parameter's pointee type says what object is at its address, so
an indexed store through a `long long *` that a `void *` round trip made
from a `long *` parameter is refused (C11 6.5p7).

```c filename=store.c
void store_param(long *p) {
    void *v = p;
    long long *q = v;
    q[0] = 3;
}
```

```click
verifying "store.c";

void store_param(long *p) {
    requires viewable(p[0..1]);
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
