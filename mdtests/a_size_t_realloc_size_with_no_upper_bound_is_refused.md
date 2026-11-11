# A `size_t` `realloc` size with no upper bound is refused

`realloc(p, m * w)` to a 64-bit count is admitted only where the facts
decide `1 <= m <= PTRDIFF_MAX / w` (`design/heap-extents.md`, stage 4).
Here they give no upper bound, so the `realloc` is refused.

```c filename=a_size_t_realloc_size_with_no_upper_bound_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int resize(size_t m) {
    uint32_t *p = malloc(4 * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, m * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    free(q);
    return 1;
}
```

```click
verifying "a_size_t_realloc_size_with_no_upper_bound_is_refused.c";

int32 resize(size_t m) {
    requires 1u64 <= m;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
