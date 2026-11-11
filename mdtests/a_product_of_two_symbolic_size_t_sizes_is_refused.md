# A product of two symbolic `size_t` sizes is refused

Both factors of `malloc(n * m)` are symbolic, so no constant element width
makes the product's exactness a decided bound on one factor. Click does not
admit it, even though both factors are bounded.

```c filename=a_product_of_two_symbolic_size_t_sizes_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int make(size_t n, size_t m) {
    uint8_t *p = malloc(n * m);
    if (p == 0) {
        return 0;
    }
    free(p);
    return 1;
}
```

```click
verifying "a_product_of_two_symbolic_size_t_sizes_is_refused.c";

int32 make(size_t n, size_t m) {
    requires 1u64 <= n and n <= 100u64;
    requires 1u64 <= m and m <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
