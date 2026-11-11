# A store through the old pointer after a 64-bit `realloc` is refused

A successful `realloc` of a 64-bit block frees the old block, so a store
through the old pointer is refused.

```c filename=a_store_through_the_old_pointer_after_a_64_bit_realloc_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int grow(size_t n, size_t m) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, m * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    p[0] = 1;
    free(q);
    return 1;
}
```

```click
verifying "a_store_through_the_old_pointer_after_a_64_bit_realloc_is_refused.c";

int32 grow(size_t n, size_t m) {
    requires 1u64 <= n and n <= 100u64 and 1u64 <= m and m <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: use of a pointer into a freed allocation
```
