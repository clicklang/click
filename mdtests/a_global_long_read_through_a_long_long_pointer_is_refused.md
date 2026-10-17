# A global `long` read through a `long long` pointer is refused

A global's declaration is authoritative, as a local's is: its block records
its type, so a `long long` read of a global `long` through a `void *` round
trip is refused (C11 6.5p7).

```c filename=globals.c
long counter;

long long read_counter(void) {
    void *v = &counter;
    long long *q = v;
    return *q;
}
```

```click
verifying "globals.c";

long long read_counter() {
    owns counter;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
