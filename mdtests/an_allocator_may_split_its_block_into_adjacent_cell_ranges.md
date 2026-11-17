# An allocator may split its block into adjacent cell ranges

`make` returns one `malloc(16)` block, possibly null. Its contract
produces `buffer(result)`, which owns the block's allocation and, when the
pointer is not null, its four `int32_t` cells as two adjacent ranges,
`p[0..1]` and `p[1..4]`. Together they cover exactly the sixteen bytes the
body allocated, so the split is accepted.

```c filename=an_allocator_may_split_its_block_into_adjacent_cell_ranges.c
#include <stdint.h>
#include <stdlib.h>

int32_t *make(void) {
    int32_t *p = malloc(16);
    return p;
}
```

```click
verifying "an_allocator_may_split_its_block_into_adjacent_cell_ranges.c";

resource buffer(p: int32_t*) {
    if p != 0 {
        owns allocation(p, 16);
        owns p[0..1];
        owns p[1..4];
    }
}

int32_t* make() {
    produces buffer(result);
}
```

```expect
pass
```
