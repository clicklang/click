# A `size_t` struct-array `calloc` block reads zero fields

Every field of a zeroed 64-bit struct-array block reads as zero, at the
first element and at `p[n - 1]`, including a byte field followed by padding.

```c filename=a_size_t_struct_array_calloc_block_reads_zero_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint8_t tag;
    int32_t value;
};

int zero(size_t n) {
    struct item *p = calloc(n, sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    int r = p[n - 1].tag + p[n - 1].value + p->value;
    free(p);
    return r;
}
```

```click
verifying "a_size_t_struct_array_calloc_block_reads_zero_fields.c";

int32 zero(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0;
}
```

```expect
pass
```
