# A bounded `size_t` `calloc` count allocates a zeroed 64-bit block

`calloc(n, sizeof(uint32_t))` with a `size_t` count `n` makes a heap block
with a 64-bit extent (`design/heap-extents.md`, stage 4). `calloc` returns
null when `n * w` is not representable, so the product is never evaluated as
C's wrapping `size_t` product: the facts must prove
`1 <= n <= PTRDIFF_MAX / w`, here that limit itself, and then the block is the
exact `n * 4u64` bytes. Its last element reads as zero before it is written.

```c filename=a_bounded_size_t_calloc_count_allocates_a_zeroed_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

uint32_t last(size_t n) {
    uint32_t *p = calloc(n, sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t r = p[n - 1];
    p[n - 1] = 5;
    free(p);
    return r;
}
```

```click
verifying "a_bounded_size_t_calloc_count_allocates_a_zeroed_64_bit_block.c";

uint32_t last(size_t n) {
    requires 1u64 <= n and n <= 2305843009213693951u64;
    ensures result == 0;
}
```

```expect
pass
```
