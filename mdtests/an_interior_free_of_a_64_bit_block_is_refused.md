# An interior free of a 64-bit block is refused

`free` of a 64-bit block requires its base, as for any block.

```c filename=an_interior_free_of_a_64_bit_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int interior(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    free(p + 1);
    return 1;
}
```

```click
verifying "an_interior_free_of_a_64_bit_block_is_refused.c";

int32 interior(size_t n) {
    requires 2u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: cannot free an interior pointer; free requires the allocation base
```
