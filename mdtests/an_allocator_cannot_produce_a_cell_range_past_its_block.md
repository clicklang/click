# An allocator cannot produce a cell range past its block

`make` returns one `malloc(16)` block, possibly null. Its contract claims
`buffer(result)` owns `p[0..1]` and `p[1..5]`: the second range runs one
cell past the sixteen bytes the body allocated, so it is refused.

```c filename=an_allocator_cannot_produce_a_cell_range_past_its_block.c
#include <stdint.h>
#include <stdlib.h>

int32_t *make(void) {
    int32_t *p = malloc(16);
    return p;
}
```

```click
verifying "an_allocator_cannot_produce_a_cell_range_past_its_block.c";

resource buffer(p: int32_t*) {
    if p != 0 {
        owns allocation(p, 16);
        owns p[0..1];
        owns p[1..5];
    }
}

int32_t* make() {
    produces buffer(result);
}
```

```expect
fail: `make.produces_0` path 0 left `make.produces_0` unproved
```
