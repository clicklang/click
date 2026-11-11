# A store after a callee frees a 64-bit block is refused

A callee that consumes a 64-bit block's `allocation` and does not give it
back may free it, and here does. The caller's later store through its stale
pointer is refused.

```c filename=a_store_after_a_callee_frees_a_64_bit_block_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, size_t n) {
    free(p);
}

int caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    release(p, n);
    p[0] = 1;
    return 1;
}
```

```click
verifying "a_store_after_a_callee_frees_a_64_bit_block_is_refused.c";

void release(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
}

int32 caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: use of a pointer into a freed allocation
```
