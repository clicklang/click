# An unbounded `size_t` `malloc` size is refused

A symbolic 64-bit size makes a heap block only where the facts prove it fits
one (`design/heap-extents.md`, D3): at least 1 and at most `PTRDIFF_MAX`
bytes, and for `malloc(n * w)` `n <= PTRDIFF_MAX / w`. There is no assumption
that `malloc` returns null for a larger size, so a count with only a lower
bound is refused at the allocation, with that reason. Replaces the 32-bit
refusal of every symbolic `size_t` size.

```c filename=an_unbounded_size_t_malloc_size_is_refused.c
#include <stdlib.h>
#include <stdint.h>

int make(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    free(p);
    return 1;
}
```

```click
verifying "an_unbounded_size_t_malloc_size_is_refused.c";

int32 make(size_t n) {
    requires 1u64 <= n;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
