# A callee frees a 64-bit block it consumes

`malloc(n * sizeof(uint32_t))` with a `size_t` count makes a block with a
64-bit extent, whose token is `allocation(p, n * 4u64)`. A callee that
`consumes allocation(p, n * 4u64)` with its range takes the block: it writes
the last element at a `size_t` index and frees it. The caller decides the
requirement's extent, `1 <= n <= PTRDIFF_MAX / 4`, from its own bound.

```c filename=a_callee_frees_a_64_bit_block_it_consumes.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, size_t n) {
    p[n - 1] = 1;
    free(p);
}

int caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    release(p, n);
    return 1;
}
```

```click
verifying "a_callee_frees_a_64_bit_block_it_consumes.c";

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
pass
```
