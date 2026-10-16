# A pointer cell read through a pointer of the other signedness is refused

Unlike the integers they point to, `long *` and `unsigned long *` are
different pointer types for aliasing: GCC 13 at `-O2` assumes a store through
`unsigned long **` leaves every `long *` unchanged. Reading a `long *` cell
through an `unsigned long **` is therefore refused, as C11 6.5p7 requires.

```c filename=cells.c
unsigned long *read_cell(long **pp) {
    void *v = pp;
    unsigned long **q = v;
    return *q;
}
```

```click
verifying "cells.c";

uint64* read_cell(int64** pp) {
    requires pp != 0;
    views *pp;
    ensures true;
} by {
    execute();
    simp();
}
```

```expect
fail: an object of type `long *` accessed through an lvalue of type `unsigned long *`
```
