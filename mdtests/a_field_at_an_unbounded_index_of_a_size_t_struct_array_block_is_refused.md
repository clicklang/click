# A field at an unbounded index of a `size_t` struct-array block is refused

Nothing relates the index `j` to the element count `n`, so `&p[j]` may leave
the block and forming it is refused.

```c filename=a_field_at_an_unbounded_index_of_a_size_t_struct_array_block_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int at(size_t n, size_t j) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    p[j].value = 3;
    free(p);
    return 1;
}
```

```click
verifying "a_field_at_an_unbounded_index_of_a_size_t_struct_array_block_is_refused.c";

int32 at(size_t n, size_t j) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
