# Stores through the object's own type are allowed

Assignment, indexed assignment, and compound assignment through a pointer of
the object's own type are ordinary accesses: the strict-aliasing check
compares the store's type with the declared `long` and allows it.

```c filename=store.c
long store_own(void) {
    long x;
    long *p = &x;
    *p = 3;
    p[0] += 1;
    return x;
}
```

```click
verifying "store.c";

long store_own() {
    ensures result == 4;
} by {
    execute();
    simp();
}
```

```expect
pass
```
