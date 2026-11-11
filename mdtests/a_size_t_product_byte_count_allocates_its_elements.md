# A `size_t` byte count that is a product allocates its elements

A byte count computed before the call, `size_t bytes = n * 4`, reaches
`malloc` as the `size_t` product itself. The facts prove the factor at most
`PTRDIFF_MAX / 4`, which makes the product exact, so the block holds `n`
`uint32_t` elements.

```c filename=a_size_t_product_byte_count_allocates_its_elements.c
#include <stdlib.h>
#include <stdint.h>

int last(size_t n) {
    size_t bytes = n * 4;
    uint32_t *p = malloc(bytes);
    if (p == 0) {
        return 0;
    }
    p[n - 1] = 1;
    free(p);
    return 1;
}
```

```click
verifying "a_size_t_product_byte_count_allocates_its_elements.c";

int32 last(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
