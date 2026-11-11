# An `int` and a `size_t` index address a 64-bit block

A block with a 64-bit extent is addressed like a `size_t` parameter range:
an `int` index is compared with the block's element count at 64 bits, and a
`size_t` index stays 64-bit.

```c filename=an_int_and_a_size_t_index_address_a_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

int store(size_t n, int i, size_t j) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[i] = 1;
    p[j] = 2;
    free(p);
    return 1;
}
```

```click
verifying "an_int_and_a_size_t_index_address_a_64_bit_block.c";

int32 store(size_t n, int32 i, size_t j) {
    requires 10u64 <= n and n <= 100u64;
    requires 0 <= i and i < 10;
    requires j < n;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
