# A store into a freed 64-bit block is refused

After `free`, a pointer into a 64-bit block is indeterminate, as for any
block.

```c filename=a_store_into_a_freed_64_bit_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int after(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    free(p);
    p[0] = 1;
    return 1;
}
```

```click
verifying "a_store_into_a_freed_64_bit_block_is_refused.c";

int32 after(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: use of a pointer into a freed allocation
```
