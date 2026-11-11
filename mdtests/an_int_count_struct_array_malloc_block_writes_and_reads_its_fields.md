# An `int` count struct-array `malloc` block writes and reads its fields

`n * sizeof(struct item)` with an `int` `n` is a `size_t` product, so the
block is 64-bit (`n` converted to `size_t`, times `8u64`). An `int` loop
index addresses its elements' fields as a `size_t` one does.

```c filename=an_int_count_struct_array_malloc_block_writes_and_reads_its_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int fill(int n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    for (int i = 0; i < n; i++) {
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
verifying "an_int_count_struct_array_malloc_block_writes_and_reads_its_fields.c";

int32 fill(int32 n) {
    requires 1 <= n and n <= 100;
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
        invariant 0 <= i and i <= n;
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
