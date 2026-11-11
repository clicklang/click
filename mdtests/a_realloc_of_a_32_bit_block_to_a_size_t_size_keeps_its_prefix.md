# A `realloc` of a 32-bit block to a `size_t` size keeps its prefix

A constant-size block has a 32-bit extent; `realloc` to a bounded `size_t`
count gives the new block a 64-bit one (`design/heap-extents.md`, stage 4).
The old block's 32-bit token and range are consumed, and its second element,
which ends at byte 8, fits `n * 4u64` because `n >= 2`.

```c filename=a_realloc_of_a_32_bit_block_to_a_size_t_size_keeps_its_prefix.c
#include <stdlib.h>
#include <stdint.h>

uint32_t widen(size_t n) {
    uint32_t *p = malloc(2 * sizeof(uint32_t));
    if (p == 0) {
        return 7;
    }
    p[1] = 7;
    uint32_t *q = realloc(p, n * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 7;
    }
    uint32_t r = q[1];
    q[n - 1] = 1;
    free(q);
    return r;
}
```

```click
verifying "a_realloc_of_a_32_bit_block_to_a_size_t_size_keeps_its_prefix.c";

uint32_t widen(size_t n) {
    requires 2u64 < n and n <= 100u64;
    ensures result == 7;
}
```

```expect
pass
```
