# A `size_t` `calloc` count with no upper bound is refused

A 64-bit `calloc` count is admitted only where the facts decide
`1 <= n <= PTRDIFF_MAX / w` (`design/heap-extents.md`, stage 4). Here they
give no upper bound, so the guard is undecided and the `calloc` is refused;
unlike `malloc`, `calloc` has no wrapped product to fall back on.

```c filename=a_size_t_calloc_count_with_no_upper_bound_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int make(size_t n) {
    uint32_t *p = calloc(n, sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    free(p);
    return 1;
}
```

```click
verifying "a_size_t_calloc_count_with_no_upper_bound_is_refused.c";

int32 make(size_t n) {
    requires 1u64 <= n;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
