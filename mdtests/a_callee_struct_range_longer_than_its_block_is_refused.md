# A callee struct range longer than its block is refused

The caller holds a `calloc(n, sizeof(struct item))` block of `n` structs and
passes `n + 1` to a callee owning `p[0..n + 1]`. The re-spelled requirement
is one struct longer than the block.

```c filename=a_callee_struct_range_longer_than_its_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void touch(struct item *p, size_t n) {
}

int make(size_t n) {
    struct item *p = calloc(n, sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    touch(p, n + 1);
    free(p);
    return 1;
}
```

```click
verifying "a_callee_struct_range_longer_than_its_block_is_refused.c";

void touch(struct item* p, size_t n) {
    owns p[0..n];
}

int32 make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: missing resource fact
```
