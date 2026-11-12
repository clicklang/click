# A callee owning a `size_t` struct range reads and writes its fields

`calloc(n, sizeof(struct item))` with a `size_t` `n` makes a 64-bit block
owned as the byte range `p[0u64..n * 8u64]`. The callee's `owns p[0..n]` is
the range `p[0u64..n]` of 8-byte structs: the call takes it from the byte
range, and the return gives it back, because the facts decide that `n * 8`
does not wrap, so both spellings name the same bytes
(`design/heap-extents.md`). The callee reads `p->value` and writes
`p[n - 1].value`, each placed over the struct count `n`; the caller reads
the field back and frees the block, whose byte range is the returned struct
range again.

```c filename=a_callee_owning_a_size_t_struct_range_reads_and_writes_its_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int set_last(struct item *p, size_t n) {
    int first = p->value;
    p[n - 1].value = 3;
    return first;
}

int make(size_t n) {
    struct item *p = calloc(n, sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    set_last(p, n);
    int r = p[n - 1].value;
    free(p);
    return r;
}
```

```click
verifying "a_callee_owning_a_size_t_struct_range_reads_and_writes_its_fields.c";

int32 set_last(struct item* p, size_t n) {
    requires 1u64 <= n and n <= 100u64;
    owns p[0..n];
    ensures p[n - 1u64].value == 3;
}

int32 make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 3;
}
```

```expect
pass
```
