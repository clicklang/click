# A call returning the 64-bit allocation it consumed is freed by the caller

`malloc(n * sizeof(uint32_t))` with a `size_t` count makes a block whose
token is `allocation(p, n * 4u64)`. A callee that consumes that token,
states `ensures result == p`, and produces `allocation(result, n * 4u64)`
continues the allocation, and the caller frees it through the returned
pointer.

```c filename=a_call_returning_the_64_bit_allocation_it_consumed_is_freed_by_the_caller.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint32_t *touch(uint32_t *p, size_t n) {
    return p;
}

int caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = touch(p, n);
    free(q);
    return 1;
}
```

```click
verifying "a_call_returning_the_64_bit_allocation_it_consumed_is_freed_by_the_caller.c";

uint32_t* touch(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
    ensures result == p;
    produces allocation(result, n * 4u64);
    produces uninitialized(result[0..n]);
}

int32 caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
