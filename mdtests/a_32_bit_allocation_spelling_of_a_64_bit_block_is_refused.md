# A 32-bit `allocation` spelling of a 64-bit block is refused

`malloc(n * sizeof(uint32_t))` with a `size_t` count holds the token
`allocation(p, n * 4u64)`, a 64-bit extent. A callee that states the block as
`allocation(p, m * 4)` with an `int32` count names a 32-bit extent. A
block's extent keeps the format of its size's C type, and tokens of the two
formats never match (`design/heap-extents.md`, D5); the refusal names both.

```c filename=a_32_bit_allocation_spelling_of_a_64_bit_block_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, int m) {
    free(p);
}

int caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    release(p, (int)n);
    return 1;
}
```

```click
verifying "a_32_bit_allocation_spelling_of_a_64_bit_block_is_refused.c";

void release(uint32_t* p, int32 m) {
    requires 1 <= m and m <= 1000;
    consumes allocation(p, m * 4);
    consumes p[0..m];
}

int32 caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: `allocation` states a 32-bit (`int32`) byte count, but the block's allocation token holds a 64-bit (`uint64`, `size_t`) one
```
