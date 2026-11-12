# A first field one past a `size_t` struct range in a callee is refused

`&p[n].key` is the one-past address of a callee's `p[0..n]` struct range,
which may be formed, but no access there is inside the range.

```c filename=a_first_field_one_past_a_size_t_struct_range_in_a_callee_is_refused.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

void set_past(struct item *p, size_t n) {
    p[n].key = 3;
}
```

```click
verifying "a_first_field_one_past_a_size_t_struct_range_in_a_callee_is_refused.c";

void set_past(struct item* p, size_t n) {
    requires 1u64 <= n and n <= 100u64;
    owns p[0..n];
}
```

```expect
fail: access outside the subobject the pointer designates
```
