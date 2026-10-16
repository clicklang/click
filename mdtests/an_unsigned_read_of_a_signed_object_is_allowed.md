# An unsigned read of a signed object is allowed

C11 6.5p7 lets an object be accessed through the signed or unsigned type
corresponding to its own, and GCC reloads after a store through either. A
`long` read through an `unsigned long *`, and through a `long *` after a
`void *` round trip, are both allowed.

```c filename=same_type.c
unsigned long read_unsigned(long *p) {
    void *v = p;
    unsigned long *q = v;
    return *q;
}

long read_back(long *p) {
    void *v = p;
    long *q = v;
    return *q;
}
```

```click
verifying "same_type.c";

uint64 read_unsigned(int64* p) {
    requires p != 0;
    views *p;
    ensures result == (uint64)*p;
} by {
    execute();
    simp();
}

int64 read_back(int64* p) {
    requires p != 0;
    views *p;
    ensures result == *p;
} by {
    execute();
    simp();
}
```

```expect
pass
```
