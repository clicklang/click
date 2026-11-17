# An allocator cannot produce more cells than it allocated

`make` returns one `malloc(16)` block, possibly null. Its contract claims
`buffer(result)` owns eight `int32_t` cells, thirty-two bytes, but the body
allocated only sixteen, so the produced resource is refused.

```c filename=an_allocator_cannot_produce_more_cells_than_it_allocated.c
#include <stdint.h>
#include <stdlib.h>

int32_t *make(void) {
    int32_t *p = malloc(16);
    return p;
}
```

```click
verifying "an_allocator_cannot_produce_more_cells_than_it_allocated.c";

resource buffer(p: int32_t*) {
    if p != 0 {
        owns allocation(p, 16);
        owns p[0..8];
    }
}

int32_t* make() {
    produces buffer(result);
}
```

```expect
fail: `make.produces_0` path 0 left `make.produces_0` unproved
```
