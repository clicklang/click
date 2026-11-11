# A symbolic `size_t` `calloc` count is refused

`calloc(n, w)` returns null when `n * w` is not representable, so its size
is never C's wrapping product. A 64-bit `calloc` size is not supported yet
(`design/heap-extents.md`, stage 4) and is refused even when bounded; so is a
`realloc` to a symbolic 64-bit size.

```c filename=a_symbolic_size_t_calloc_count_is_refused.c
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
verifying "a_symbolic_size_t_calloc_count_is_refused.c";

int32 make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: heap allocation size must be proved to fit a heap block
```
