# A loop owning a `size_t` struct range writes its fields

A loop over a `malloc(n * sizeof(struct item))` block declares
`owns p[0..n]`, the range `p[0u64..n]` of 8-byte structs. The enclosing
function holds the block as the byte range `p[0u64..n * 8u64]`; the loop
takes the struct range from it and gives it back at its exit, since `n * 8`
is decided not to wrap. The body writes both fields of each element through
the struct range.

```c filename=a_loop_owning_a_size_t_struct_range_writes_its_fields.c
#include <stdlib.h>
#include <stdint.h>

struct item {
    uint32_t key;
    int32_t value;
};

int fill(size_t n) {
    struct item *p = malloc(n * sizeof(struct item));
    if (p == 0) {
        return 0;
    }
    for (size_t i = 0; i < n; i++) {
        p[i].key = 0;
        p[i].value = 7;
    }
    p[n - 1].value = 3;
    int r = p[n - 1].value;
    free(p);
    return r;
}
```

```click
verifying "a_loop_owning_a_size_t_struct_range_writes_its_fields.c";

int32 fill(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 3;
} by {
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    step_until(loop(0));
    loop {
        decreases n - i;
        owns p[0..n];
        invariant i <= n;
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
