# A returned allocation of the other extent format is refused

`shrink` consumes a 64-bit block and returns a block with a 32-bit extent
that may be the same pointer. Whether the call continues the allocation or
frees it is decided by comparing the two extents, and extents of different
formats are never one allocation's (`design/heap-extents.md`, D5), so the
call is refused rather than compared.

```c filename=a_returned_allocation_of_the_other_extent_format_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint32_t *shrink(uint32_t *p, size_t n);

int caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = shrink(p, n);
    free(q);
    return 1;
}
```

```click
verifying "a_returned_allocation_of_the_other_extent_format_is_refused.c";

extern uint32_t* shrink(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
    ensures result != 0;
    produces allocation(result, 4);
    produces uninitialized(result[0..1]);
}

int32 caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: the call consumes an allocation with a 64-bit (`uint64`, `size_t`) byte count and returns one that may be the same block with a 32-bit (`int32`) byte count
```
