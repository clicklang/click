# A declared `long` read through a `long long` pointer is refused

A declared object's type is authoritative: whatever pointer later reaches it,
an access must use a type compatible with the declaration (C11 6.5p7). A
local `long`, and a local `long long` array, are refused when a `void *`
round trip hands them to a pointer of the other rank.

```c filename=declared.c
long long read_local(void) {
    long value = 7;
    void *v = &value;
    long long *q = v;
    return *q;
}

long read_array(void) {
    long long values[2];
    values[0] = 1;
    values[1] = 2;
    void *v = values;
    long *q = v;
    return q[1];
}
```

```click
verifying "declared.c";

long long read_local() {
    ensures result == 7;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
