# A 64-bit `allocation` requirement is assumed at entry

A callee's `consumes allocation(p, n * 4u64)` is established by each caller,
which decides `1 <= n <= PTRDIFF_MAX / 4` where it calls
(`mdtests/a_call_naming_a_64_bit_extent_with_an_unbounded_count_is_refused.md`).
The callee assumes it, so its contract needs no bound on `n` of its own to
free the block.

```c filename=a_64_bit_allocation_requirement_is_assumed_at_entry.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, size_t n) {
    free(p);
}
```

```click
verifying "a_64_bit_allocation_requirement_is_assumed_at_entry.c";

void release(uint32_t* p, size_t n) {
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
}
```

```expect
pass
```
