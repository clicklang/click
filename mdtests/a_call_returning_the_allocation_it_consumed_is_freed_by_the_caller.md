# A call returning the allocation it consumed is freed by the caller

A callee that consumes `allocation(p, n * 4)`, states `ensures result == p`,
and produces `allocation(result, n * 4)` lends the block and gives it back.
The call continues the allocation: the caller holds its token again, under
the block it allocated, and frees it through the returned pointer.

```c filename=a_call_returning_the_allocation_it_consumed_is_freed_by_the_caller.c
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
    return 1;
}
```

```click
verifying "a_call_returning_the_allocation_it_consumed_is_freed_by_the_caller.c";

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
pass
```
