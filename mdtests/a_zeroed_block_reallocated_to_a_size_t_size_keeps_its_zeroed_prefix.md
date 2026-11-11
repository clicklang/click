# A zeroed block reallocated to a `size_t` size keeps its zeroed prefix

A `calloc` block of 16 bytes grows with `realloc` to a bounded `size_t`
count. The zeroed prefix stays the constant 16: the facts decide the new
extent `n * 4u64` is at least 16 bytes (`4 <= n`), so all of the old block
reads as zero in the new one (`design/heap-extents.md`, stage 4).

```c filename=a_zeroed_block_reallocated_to_a_size_t_size_keeps_its_zeroed_prefix.c
#include <stdlib.h>
#include <stdint.h>

uint32_t zgrow(size_t n) {
    uint32_t *p = calloc(4, sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    uint32_t *q = realloc(p, n * sizeof(uint32_t));
    if (q == 0) {
        free(p);
        return 0;
    }
    uint32_t r = q[3];
    q[n - 1] = 1;
    free(q);
    return r;
}
```

```click
verifying "a_zeroed_block_reallocated_to_a_size_t_size_keeps_its_zeroed_prefix.c";

uint32_t zgrow(size_t n) {
    requires 4u64 <= n and n <= 100u64;
    ensures result == 0;
}
```

```expect
pass
```
