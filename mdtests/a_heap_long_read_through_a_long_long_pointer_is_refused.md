# A heap `long` read through a `long long` pointer is refused

Allocated storage has no declared type: a store gives the cell it writes the
type of its lvalue (C11 6.5p6). A `long` stored into fresh `malloc` storage
and read back through a `long long *` after a `void *` round trip is refused.

```c filename=heap.c
#include <stdlib.h>

long long rank(void) {
    long *p = malloc(sizeof(long));
    if (!p) return 0;
    *p = 7;
    void *v = p;
    long long *q = v;
    long long r = *q;
    free(p);
    return r;
}
```

```click
verifying "heap.c";

long long rank() {
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
