# A bounded `size_t` element count allocates a 64-bit block

`malloc(n * sizeof(uint32_t))` with a `size_t` count `n` makes a heap block
with a 64-bit extent (`design/heap-extents.md`, stage 2): its `allocation`
token holds the `uint64` byte count `n * 4u64` and it is owned as
`p[0..n]` with 64-bit indices. The facts must prove
`1 <= n <= PTRDIFF_MAX / 4`, so the product is exact; here the bound is that
limit itself, far past the 32-bit extent. The last element is written and
read at a `size_t` index and the block is freed.

```c filename=a_bounded_size_t_element_count_allocates_a_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

uint32_t last(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[n - 1] = 5;
    uint32_t r = p[n - 1];
    free(p);
    return r;
}
```

```click
verifying "a_bounded_size_t_element_count_allocates_a_64_bit_block.c";

uint32_t last(size_t n) {
    requires 1u64 <= n and n <= 2305843009213693951u64;
    ensures result == 0 or result == 5;
}
```

```expect
pass
```
