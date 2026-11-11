# A 64-bit `allocation` spelling of a 32-bit block is refused

`malloc(m * 4)` with an `int` count holds a 32-bit extent,
`allocation(p, m * 4)`. A callee that states the block with a `size_t` count,
`allocation(p, n * 4u64)`, names a 64-bit extent, which does not match it
(`design/heap-extents.md`, D5); the refusal names both formats.

```c filename=a_64_bit_allocation_spelling_of_a_32_bit_block_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, size_t n) {
    free(p);
}

int caller(int m) {
    uint32_t *p = malloc(m * 4);
    if (p == 0) {
        return 0;
    }
    release(p, (size_t)m);
    return 1;
}
```

```click
verifying "a_64_bit_allocation_spelling_of_a_32_bit_block_is_refused.c";

void release(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n * 4u64);
    consumes p[0..n];
}

int32 caller(int32 m) {
    requires 1 <= m and m <= 1000;
    ensures result == 0 or result == 1;
}
```

```expect
fail: `allocation` states a 64-bit (`uint64`, `size_t`) byte count, but the block's allocation token holds a 32-bit (`int32`) one
```
