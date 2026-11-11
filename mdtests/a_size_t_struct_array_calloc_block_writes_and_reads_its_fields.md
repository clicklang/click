# A `size_t` struct-array `calloc` block writes and reads its fields

`calloc(n, sizeof(struct item))` with a `size_t` `n` evaluates only the count
and makes a zeroed 64-bit block of `n * 8u64` bytes. Its fields are written
in a loop and at `p[n - 1]` as for a `malloc` block.

```c filename=a_size_t_struct_array_calloc_block_writes_and_reads_its_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int fill(size_t n) {
    struct item *p = calloc(n, sizeof(struct item));
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
verifying "a_size_t_struct_array_calloc_block_writes_and_reads_its_fields.c";

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
