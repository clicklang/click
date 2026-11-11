# A wrapping `size_t` product allocates only the wrapped bytes

`size_t` arithmetic wraps without undefined behavior: with
`n == 2^62 + 1`, `n * sizeof(uint32_t)` is 4, and `malloc` allocates a real
4-byte block. Click takes the wrapped product as the size, not `n` elements:
`p[0]` is in the block and `p[1]` is refused.

```c filename=a_wrapping_size_t_product_allocates_only_the_wrapped_bytes.c
#include <stdlib.h>
#include <stdint.h>

int make(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[0] = 1;
    p[1] = 2;
    free(p);
    return 1;
}
```

```click
verifying "a_wrapping_size_t_product_allocates_only_the_wrapped_bytes.c";

int32 make(size_t n) {
    requires n == 4611686018427387905u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: missing resource fact `owns ((char *)p)[4..8]`
```
