# A store past a reallocated 64-bit block is refused

After `realloc` to `m * sizeof(uint32_t)` bytes the new block owns
`q[0..m]` with 64-bit indices; `q[m]` is one past it and is refused.

```c filename=a_store_past_a_reallocated_64_bit_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int grow(size_t m) {
    uint32_t *p = malloc(4 * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, m * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    q[m] = 1;
    free(q);
    return 1;
}
```

```click
verifying "a_store_past_a_reallocated_64_bit_block_is_refused.c";

int32 grow(size_t m) {
    requires 1u64 <= m and m <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: missing resource fact `owns ((char *)q)[(m * 4)..((m + 1) * 4)]`
```
