# A store past a 64-bit block is refused

The block of `malloc(n * sizeof(uint32_t))` holds `n` elements; `p[n]` is
one past its end and is refused.

```c filename=a_store_past_a_64_bit_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int past(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[n] = 1;
    free(p);
    return 1;
}
```

```click
verifying "a_store_past_a_64_bit_block_is_refused.c";

int32 past(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: missing resource fact `owns ((char *)p)[(n * 4)..((n + 1) * 4)]`
```
