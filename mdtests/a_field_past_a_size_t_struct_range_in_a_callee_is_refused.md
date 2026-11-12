# A field past a `size_t` struct range in a callee is refused

A callee owning `p[0..n]` of 8-byte structs forms `&p[n]`, one past the
range, but `&p[n].value` lies past it: the field address of element `i` is
placed only for `i < n`.

```c filename=a_field_past_a_size_t_struct_range_in_a_callee_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void set_past(struct item *p, size_t n) {
    p[n].value = 3;
}
```

```click
verifying "a_field_past_a_size_t_struct_range_in_a_callee_is_refused.c";

void set_past(struct item* p, size_t n) {
    requires 1u64 <= n and n <= 100u64;
    owns p[0..n];
}
```

```expect
fail: pointer arithmetic left the pointed-to object
```
