# A heap `long` written at a computed index and read through a `long long` pointer is refused

A store at a computed index gives its heap cell the type of its lvalue, as a
store at a constant offset does (C11 6.5p6). A `long` stored at `p[i]` and
read back at the same index through a `long long *` is refused.

```c filename=heap.c
#include <stdlib.h>

long long rank(unsigned i) {
    long *p = malloc(4 * sizeof(long));
    if (!p) return 0;
    p[i] = 7;
    void *v = p;
    long long *q = v;
    long long r = q[i];
    free(p);
    return r;
}
```

```click
verifying "heap.c";

long long rank(uint32 i) {
    requires i < 4;
    ensures true;
} by {
    execute();
}
```

```expect
fail: an object of type `long` accessed through an lvalue of type `long long`
```
