# A `size_t` struct-array block is accessed after a call taking its allocation

The callee borrows the block's `allocation(p, n * 8u64)` token and gives it
back; its entry assumes the token's extent. After the call the caller writes
and reads a field of the last element and frees the block.

```c filename=a_size_t_struct_array_block_is_accessed_after_a_call_taking_its_allocation.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void keep(struct item *p, size_t n) {
}

int make(size_t n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    keep(p, n);
    p[n - 1].value = 2;
    int r = p[n - 1].value;
    free(p);
    return r;
}
```

```click
verifying "a_size_t_struct_array_block_is_accessed_after_a_call_taking_its_allocation.c";

void keep(struct item* p, size_t n) {
    requires 1u64 <= n;
    owns allocation(p, n * 8u64);

}

int32 make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 2;
}
```

```expect
pass
```
