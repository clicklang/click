# A `long` read through a `long long` pointer is refused

`long` and `long long` have the same size and representation on x86-64, but
they are distinct types, and C11 6.5p7 lets an object be accessed only
through its own type, up to signedness and qualifiers, or a character type.
GCC at `-O2` assumes a store through `long long *` leaves every `long`
unchanged, so a read through the wrong one of the two is refused, even after
a `void *` round trip hides the conversion from the frontend.

```c filename=rank.c
long long read_through(long *p) {
    void *v = p;
    long long *q = v;
    return *q;
}
```

```click
verifying "rank.c";

long long read_through(int64* p) {
    requires p != 0;
    views *p;
    ensures result == *p;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
