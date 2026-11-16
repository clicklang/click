# A store after freeing an allocation a call returned is refused

A callee that consumes `allocation(p, n * 4)`, states `ensures result == p`,
and produces `allocation(result, n * 4)` gives the caller back the block it
lent. Freeing it through the returned pointer `q` ends the block for `p`
too, so a later store through `p` is a use after free.

```c filename=a_store_after_freeing_an_allocation_a_call_returned_is_refused.c
#include <stdint.h>
#include <stdlib.h>

uint32_t *touch(uint32_t *p, int n) {
    return p;
}

int caller(int n) {
    uint32_t *p = malloc(n * 4);
    if (p == 0) {
        return 0;
    }
    uint32_t *q = touch(p, n);
    free(q);
    p[0] = 1;
    return 1;
}
```

```click
verifying "a_store_after_freeing_an_allocation_a_call_returned_is_refused.c";

uint32_t* touch(uint32_t* p, int32 n) {
    requires 1 <= n and n <= 1000;
    consumes allocation(p, n * 4);
    consumes uninitialized(p[0..n]);
    ensures result == p;
    produces allocation(result, n * 4);
    produces uninitialized(result[0..n]);
}

int32 caller(int32 n) {
    requires 1 <= n and n <= 1000;
    ensures result == 0 or result == 1;
}
```

```expect
fail: use of a pointer into a freed allocation
```
