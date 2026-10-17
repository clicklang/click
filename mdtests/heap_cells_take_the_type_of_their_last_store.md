# Heap cells take the type of their last store

A heap cell read through the type it was stored through verifies, and a
store through another type gives the cell that type (C11 6.5p6), so a read
through the new type verifies too, also at a computed index.

```c filename=heap.c
#include <stdlib.h>

long own(void) {
    long *p = malloc(sizeof(long));
    if (!p) return 0;
    *p = 7;
    long r = *p;
    free(p);
    return r;
}

long retype(void) {
    long long *p = malloc(sizeof(long long));
    if (!p) return 0;
    *p = 1;
    void *v = p;
    long *q = v;
    *q = 2;
    long r = *q;
    free(p);
    return r;
}

long retype_at(unsigned i) {
    long long *p = malloc(4 * sizeof(long long));
    if (!p) return 0;
    p[i] = 1;
    void *v = p;
    long *q = v;
    q[i] = 2;
    long r = q[i];
    free(p);
    return r;
}
```

```click
verifying "heap.c";

long own() {
    ensures result == 7 or result == 0;
} by {
    execute();
    simp();
}

long retype() {
    ensures result == 2 or result == 0;
} by {
    execute();
    simp();
}

long retype_at(uint32 i) {
    requires i < 4;
    ensures result == 2 or result == 0;
} by {
    execute();
    simp();
}
```

```expect
pass
```
