# Freeing a returned allocation invalidates its original alias

Returning the same allocation transfers its cleanup obligation, but does not
create another lifetime. A write through `p` after `free(q)` is refused.

```c filename=pass_through.c
#include <stdlib.h>
int *pass(int *p) { return p; }
int caller(void) {
    int *p = malloc(4);
    if (p == 0) return 0;
    int *q = pass(p);
    free(q);
    p[0] = 1;
    return 1;
}
```

```click
verifying "pass_through.c";
int32* pass(int32* p) {
    consumes allocation(p, 4);
    consumes uninitialized(p[0..1]);
    ensures result == p;
    produces allocation(result, 4);
    produces uninitialized(result[0..1]);
}
int32 caller() { ensures result == 0 or result == 1; }
```

```expect
fail: use of a pointer into a freed allocation
```
