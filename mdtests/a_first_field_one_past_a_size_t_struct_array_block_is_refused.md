# A first field one past a `size_t` struct-array block is refused

`&p[n].key` is the block's one-past-the-end address, which may be formed, but
the store through it lies outside the block, so it owns no cell there.

```c filename=a_first_field_one_past_a_size_t_struct_array_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int past(size_t n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    p[n].key = 3;
    free(p);
    return 1;
}
```

```click
verifying "a_first_field_one_past_a_size_t_struct_array_block_is_refused.c";

int32 past(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: missing resource fact
```
