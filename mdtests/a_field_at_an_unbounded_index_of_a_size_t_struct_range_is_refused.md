# A field at an unbounded index of a `size_t` struct range is refused

A callee owning `p[0..n]` of 8-byte structs writes `p[i].value` for an
index `i` the facts do not bound by `n`.

```c filename=a_field_at_an_unbounded_index_of_a_size_t_struct_range_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void set_past(struct item *p, size_t n, size_t i) {
    p[i].value = 3;
}
```

```click
verifying "a_field_at_an_unbounded_index_of_a_size_t_struct_range_is_refused.c";

void set_past(struct item* p, size_t n, size_t i) {
    requires 1u64 <= n and n <= 100u64;
    owns p[0..n];
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
