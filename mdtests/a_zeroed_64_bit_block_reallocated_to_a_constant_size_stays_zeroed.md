# A zeroed 64-bit block reallocated to a constant size stays zeroed

A `calloc` block with the 64-bit extent `n * 4u64` is resized to 16 bytes.
The facts decide `16 <= n * 4u64` (`4 <= n`), so the new block's zeroed
prefix is the constant 16, all of it (`design/heap-extents.md`, stage 4). A
prefix that is not a constant, such as growing this block to `n + 1`
elements, is not modeled.

```c filename=a_zeroed_64_bit_block_reallocated_to_a_constant_size_stays_zeroed.c
#include <stdlib.h>
#include <stdint.h>

uint32_t zshrink(size_t n) {
    uint32_t *p = calloc(n, sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, 4 * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    uint32_t r = q[3];
    free(q);
    return r;
}
```

```click
verifying "a_zeroed_64_bit_block_reallocated_to_a_constant_size_stays_zeroed.c";

uint32_t zshrink(size_t n) {
    requires 4u64 <= n and n <= 100u64;
    ensures result == 0;
}
```

```expect
pass
```
