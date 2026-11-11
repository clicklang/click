# A `realloc` shrinks a 64-bit block and keeps its prefix

A 64-bit block shrunk by one element with `realloc(p, (n - 1) * sizeof(uint32_t))`
keeps its first element: with `n >= 2` the new count is at least 1, so the
initialized bytes `0..4` lie inside the new block (`design/heap-extents.md`,
stage 4).

```c filename=a_realloc_shrinks_a_64_bit_block_and_keeps_its_prefix.c
#include <stdlib.h>
#include <stdint.h>

uint32_t shrink(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 7;
    }
    p[0] = 7;
    uint32_t *q = realloc(p, (n - 1) * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 7;
    }
    uint32_t r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_realloc_shrinks_a_64_bit_block_and_keeps_its_prefix.c";

uint32_t shrink(size_t n) {
    requires 2u64 <= n and n <= 100u64;
    ensures result == 7;
}
```

```expect
pass
```
