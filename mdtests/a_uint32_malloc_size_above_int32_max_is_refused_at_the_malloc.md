# A `uint32` `malloc` size above `INT32_MAX` is refused at the `malloc`

A heap block's extent is a checked signed 32-bit byte count
(`design/heap-extents.md`). A `uint32` size the facts do not bound by
`INT32_MAX` (2147483647) cannot be that extent, so the allocation itself is
refused and names the bound. A size of 2^31 or more used to be admitted and
read as a negative extent, so the first valid access, `p[0] = 1`, was
misreported as pointer arithmetic leaving the object.

```c filename=a_uint32_malloc_size_above_int32_max_is_refused_at_the_malloc.c
#include <stdlib.h>
#include <stdint.h>

int big(uint32_t n) {
    uint8_t *p = malloc(n);
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
verifying "a_uint32_malloc_size_above_int32_max_is_refused_at_the_malloc.c";

int32 big(uint32 n) {
    requires 1u32 <= n and n <= 3000000000u32;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be known to fit the signed 32-bit heap extent
```
