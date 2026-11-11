# A `realloc` grows a 64-bit block and keeps its prefix

`realloc(p, m * sizeof(uint32_t))` of a 64-bit block to a larger bounded
`size_t` count (`design/heap-extents.md`, stage 4) consumes the old block's
`uint64` token and wide range and gives the new block the exact extent
`m * 4u64`. The fit of the old block's initialized first element is decided
over the element count (`1 <= m`), not over the wrapping product, so its value
survives; the grown tail is writable up to `q[m - 1]`.

```c filename=a_realloc_grows_a_64_bit_block_and_keeps_its_prefix.c
#include <stdlib.h>
#include <stdint.h>

uint32_t grow(size_t n, size_t m) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 7;
    }
    p[0] = 7;
    uint32_t *q = realloc(p, m * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 7;
    }
    uint32_t r = q[0];
    q[m - 1] = 1;
    free(q);
    return r;
}
```

```click
verifying "a_realloc_grows_a_64_bit_block_and_keeps_its_prefix.c";

uint32_t grow(size_t n, size_t m) {
    requires 1u64 <= n and n < m and m <= 2305843009213693951u64;
    ensures result == 7;
}
```

```expect
pass
```
