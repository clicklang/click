# A zeroed block reallocated to an `int` size keeps its zeroed prefix

A `calloc` block of 16 bytes grows with `realloc` to a symbolic `int` count,
a 32-bit extent. The zeroed prefix is the constant 16 because the facts
decide the new size `n * 4` is at least 16 bytes, the rule a 64-bit size uses
too (`a_zeroed_block_reallocated_to_a_size_t_size_keeps_its_zeroed_prefix.md`).

```c filename=a_zeroed_block_reallocated_to_an_int_size_keeps_its_zeroed_prefix.c
#include <stdlib.h>
#include <stdint.h>

uint32_t zgrow(int n) {
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
verifying "a_zeroed_block_reallocated_to_an_int_size_keeps_its_zeroed_prefix.c";

uint32_t zgrow(int n) {
    requires 4 <= n and n <= 100;
    ensures result == 0;
}
```

```expect
pass
```
