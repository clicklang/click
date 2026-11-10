# A `uint32` element count past the `int32` heap extent is refused

`malloc(n * sizeof(uint32_t))` with a `uint32` count gives a block of
`4 * n` bytes, and the heap extent is a checked signed 32-bit byte count
(`design/heap-extents.md`). The count must be bounded by `INT32_MAX / 4`
(536870911). A bound of `INT32_MAX / 2` lets the byte count reach
4294967292, which an `int32` extent cannot hold, so the `malloc` is
refused and names the bound. It used to be admitted with that product
stored as the block's `int32` extent.

```c filename=a_uint32_element_count_above_the_int32_heap_extent_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int fill(uint32_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[0] = 1;
    int r = p[0];
    free(p);
    return r;
}
```

```click
verifying "a_uint32_element_count_above_the_int32_heap_extent_is_refused.c";

int32 fill(uint32 n) {
    requires 1u32 <= n and n <= 1073741823u32;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be known to fit the signed 32-bit heap extent
```
