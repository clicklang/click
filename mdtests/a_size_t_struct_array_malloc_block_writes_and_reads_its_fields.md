# A `size_t` struct-array `malloc` block writes and reads its fields

`malloc(n * sizeof(struct item))` with a `size_t` `n` decided
`1 <= n <= PTRDIFF_MAX / 8` makes a 64-bit block of `n * 8u64` bytes
(`design/heap-extents.md`). A loop over a `size_t` index writes both fields
of every element, then the last element's field is written and read back.
Each field address and access is placed over the element count: `p[i].value`
is inside the block when `i < n`, which the facts about `n` decide, where
the byte comparison with the wrapping product `n * 8u64` would not.

```c filename=a_size_t_struct_array_malloc_block_writes_and_reads_its_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int fill(size_t n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    for (size_t i = 0; i < n; i++) {
        p[i].key = 0;
        p[i].value = 7;
    }
    p[n - 1].value = 3;
    int r = p[n - 1].value;
    free(p);
    return r;
}
```

```click
verifying "a_size_t_struct_array_malloc_block_writes_and_reads_its_fields.c";

int32 fill(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 3;
} by {
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
