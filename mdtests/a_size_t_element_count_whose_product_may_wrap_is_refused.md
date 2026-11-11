# A `size_t` element count whose product may wrap is refused

With `n <= 2^62`, `n * 8` may wrap. The facts do not prove
`n <= PTRDIFF_MAX / 8`, so `malloc` takes C's `size_t` product as the byte
count, and a symbolic product is admitted only under that same bound. The
allocation is refused rather than read as `n` elements.

```c filename=a_size_t_element_count_whose_product_may_wrap_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int make(size_t n) {
    uint64_t *p = malloc(n * sizeof(uint64_t));
    if (p == 0) {
        return 0;
    }
    free(p);
    return 1;
}
```

```click
verifying "a_size_t_element_count_whose_product_may_wrap_is_refused.c";

int32 make(size_t n) {
    requires 1u64 <= n and n <= 4611686018427387904u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
