# A callee keeps a 64-bit block its caller frees

A callee that `owns allocation(p, n * 4u64)` borrows a 64-bit block and gives
the same token back, so the call continues the allocation rather than
retiring it. The caller then writes its last element and frees it.

```c filename=a_callee_keeps_a_64_bit_block_its_caller_frees.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void keep(uint32_t *p, size_t n) {
}

uint32_t caller(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    keep(p, n);
    p[n - 1] = 2;
    uint32_t r = p[n - 1];
    free(p);
    return r;
}
```

```click
verifying "a_callee_keeps_a_64_bit_block_its_caller_frees.c";

void keep(uint32_t* p, size_t n) {
    requires 1u64 <= n;
    owns allocation(p, n * 4u64);
    owns uninitialized(p[0..n]);
}

uint32_t caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0u32 or result == 2u32;
}
```

```expect
pass
```
