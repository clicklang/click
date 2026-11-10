# A 64-bit block freed twice is refused

Freeing a block with a 64-bit extent ends its lifetime as for any block, so
a second `free` is refused.

```c filename=a_64_bit_block_freed_twice_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int twice(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    free(p);
    free(p);
    return 1;
}
```

```click
verifying "a_64_bit_block_freed_twice_is_refused.c";

int32 twice(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: cannot free an allocation whose lifetime has already ended
```
