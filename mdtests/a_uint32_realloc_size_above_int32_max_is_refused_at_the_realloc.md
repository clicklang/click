# A `uint32` `realloc` size above `INT32_MAX` is refused at the `realloc`

`realloc` admits its new size as `malloc` does: a `uint32` byte count
must be bounded by `INT32_MAX` to fit the checked signed 32-bit heap extent
(`design/heap-extents.md`). A bound of 3000000000 is not enough, and the
`realloc` is refused and names the bound, rather than its result's first
access being misreported as leaving the object.

```c filename=a_uint32_realloc_size_above_int32_max_is_refused_at_the_realloc.c
#include <stdlib.h>
#include <stdint.h>

int grow(uint32_t n) {
    uint8_t *p = malloc(4);
    if (p == 0) {
        return 0;
    }
    uint8_t *q = realloc(p, n);
    if (q == 0) {
        free(p);
        return 0;
    }
    q[0] = 1;
    int r = q[0];
    free(q);
    return r;
}
```

```click
verifying "a_uint32_realloc_size_above_int32_max_is_refused_at_the_realloc.c";

int32 grow(uint32 n) {
    requires 4u32 <= n and n <= 3000000000u32;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be known to fit the signed 32-bit heap extent
```
