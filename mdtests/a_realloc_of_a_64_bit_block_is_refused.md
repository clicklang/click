# A `realloc` of a 64-bit block is refused

`realloc` of a block with a 64-bit extent, or to a symbolic 64-bit size, is
not supported yet (`design/heap-extents.md`, stage 4) and is refused at the
`realloc`.

```c filename=a_realloc_of_a_64_bit_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int grow(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, n * 2 * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    free(q);
    return 1;
}
```

```click
verifying "a_realloc_of_a_64_bit_block_is_refused.c";

int32 grow(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
