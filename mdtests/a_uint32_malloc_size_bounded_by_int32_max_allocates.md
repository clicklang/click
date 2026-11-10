# A `uint32` `malloc` size bounded by `INT32_MAX` allocates

A `uint32` byte count bounded by `INT32_MAX`, or a `uint32` element
count bounded by `INT32_MAX` divided by the element size, fits the checked
signed 32-bit heap extent (`design/heap-extents.md`). The block is usable
up to its last element and is freed. Sizes past those bounds are refused at
the allocation
(`a_uint32_malloc_size_above_int32_max_is_refused_at_the_malloc.md`).

```c filename=a_uint32_malloc_size_bounded_by_int32_max_allocates.c
#include <stdlib.h>
#include <stdint.h>

int bytes(uint32_t n) {
    uint8_t *p = malloc(n);
    if (p == 0) {
        return 0;
    }
    p[n - 1] = 1;
    int r = p[n - 1];
    free(p);
    return r;
}

int words(uint32_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    p[n - 1] = 1;
    int r = p[n - 1];
    free(p);
    return r;
}
```

```click
verifying "a_uint32_malloc_size_bounded_by_int32_max_allocates.c";

int32 bytes(uint32 n) {
    requires 1u32 <= n and n <= 2147483647u32;
    ensures result == 0 or result == 1;
}

int32 words(uint32 n) {
    requires 1u32 <= n and n <= 536870911u32;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
