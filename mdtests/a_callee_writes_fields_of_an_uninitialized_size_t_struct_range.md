# A callee writes fields of an uninitialized `size_t` struct range

`malloc(n * sizeof(struct item))` with a `size_t` `n` is an uninitialized
64-bit block of `n * 8u64` bytes. A callee owning `uninitialized(p[0..n])`
takes it as `n` structs, writes a field of the last and of the first, and
returns it; the caller frees the block.

```c filename=a_callee_writes_fields_of_an_uninitialized_size_t_struct_range.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void set_last(struct item *p, size_t n) {
    p[n - 1].value = 3;
    p->key = 1;
}

int make(size_t n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    set_last(p, n);
    free(p);
    return 1;
}
```

```click
verifying "a_callee_writes_fields_of_an_uninitialized_size_t_struct_range.c";

void set_last(struct item* p, size_t n) {
    requires 1u64 <= n and n <= 100u64;
    owns uninitialized(p[0..n]);
}

int32 make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
}
```

```expect
pass
```
