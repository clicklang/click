# An allocator cannot produce one cell twice

`make` returns one `malloc(16)` block, possibly null. Its contract claims
`buffer(result)` owns the cell `p[0..1]` twice. One allocation holds one
unit of each cell, so the second copy is refused.

```c filename=an_allocator_cannot_produce_one_cell_twice.c
#include <stdint.h>
#include <stdlib.h>

int32_t *make(void) {
    int32_t *p = malloc(16);
    return p;
}
```

```click
verifying "an_allocator_cannot_produce_one_cell_twice.c";

resource buffer(p: int32_t*) {
    if p != 0 {
        owns allocation(p, 16);
        owns p[0..1];
        owns p[0..1];
    }
}

int32_t* make() {
    produces buffer(result);
}
```

```expect
fail: `make.produces_0` path 0 left `make.produces_0` unproved
```
