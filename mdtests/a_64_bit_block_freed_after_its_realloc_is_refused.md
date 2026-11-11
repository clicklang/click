# A 64-bit block freed after its `realloc` is refused

A successful `realloc` of a 64-bit block ends the old block's lifetime;
freeing the old pointer afterwards is a double free and is refused.

```c filename=a_64_bit_block_freed_after_its_realloc_is_refused.c
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
    free(q);
    free(p);
    return 1;
}
```

```click
verifying "a_64_bit_block_freed_after_its_realloc_is_refused.c";

int32 grow(size_t n, size_t m) {
    requires 1u64 <= n and n <= 100u64 and 1u64 <= m and m <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: cannot free an allocation whose lifetime has already ended
```
