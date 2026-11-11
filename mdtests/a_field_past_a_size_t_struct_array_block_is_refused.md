# A field past a `size_t` struct-array block is refused

`&p[n]` is the one-past-the-end address of an `n`-element block, but its
`value` field lies past the block's `n * 8` bytes, so forming it is
undefined behavior.

```c filename=a_field_past_a_size_t_struct_array_block_is_refused.c
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
    p[n].value = 3;
    free(p);
    return 1;
}
```

```click
verifying "a_field_past_a_size_t_struct_array_block_is_refused.c";

int32 past(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
