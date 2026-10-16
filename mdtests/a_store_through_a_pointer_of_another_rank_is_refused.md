# A store through a pointer of another rank is refused

C11 6.5p7 constrains writes as well as reads. A declared `long` written
through a `long long *` is refused after a `void *` round trip hides the
conversion from the frontend.

```c filename=store.c
long store_local(void) {
    long value = 7;
    void *v = &value;
    long long *q = v;
    *q = 3;
    return value;
}
```

```click
verifying "store.c";

long store_local() {
    ensures result == 3;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
