# A `size_t` byte count `len + 1` allocates a 64-bit block

`malloc(len + 1)` for a `size_t` `len` is a raw 64-bit byte count. The facts
bound `len`, so the sum is at least 1 and at most `PTRDIFF_MAX` and does not
wrap; the byte at index `len` is the block's last.

```c filename=a_size_t_byte_count_plus_one_allocates_a_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

int terminate(size_t len) {
    uint8_t *p = malloc(len + 1);
    if (p == 0) {
        return 0;
    }
    p[len] = 0;
    free(p);
    return 1;
}
```

```click
verifying "a_size_t_byte_count_plus_one_allocates_a_64_bit_block.c";

int32 terminate(size_t len) {
    requires len <= 4096u64;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
