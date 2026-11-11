# A `calloc` count whose product would wrap is refused

With `n == 2^62 + 1`, `n * 4` wraps to 4 as a `size_t` product, and
`malloc(n * 4)` allocates those 4 bytes
(`a_wrapping_size_t_product_allocates_only_the_wrapped_bytes.md`). `calloc(n, 4)`
instead returns null because `n * 4` is not representable, so it never
evaluates the product (`design/heap-extents.md`, stage 4): its count fails
`n <= PTRDIFF_MAX / 4` and the `calloc` is refused rather than modeled as a
4-byte block.

```c filename=a_calloc_count_whose_product_would_wrap_is_refused.c
#include <stdlib.h>
#include <stdint.h>

uint32_t first(size_t n) {
    uint32_t *p = calloc(n, sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t r = p[0];
    free(p);
    return r;
}
```

```click
verifying "a_calloc_count_whose_product_would_wrap_is_refused.c";

uint32_t first(size_t n) {
    requires n == 4611686018427387905u64;
    ensures result == 0;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
