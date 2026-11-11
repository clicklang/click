# An extern allocator states a `size_t` extent

An allocator that takes a `size_t` byte count states its block's extent as
that count: `allocation(result, bytes)` with a `uint64` byte count is a heap
block with a 64-bit extent (`design/heap-extents.md`, stage 3), owned as
`result[0..bytes]` with 64-bit indices. Where the caller's facts bound the
count, `1 <= n <= PTRDIFF_MAX`, the returned token is admitted; the caller
writes the last and the first byte at `size_t` indices and frees the block.

```c filename=an_extern_allocator_states_a_size_t_extent.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint8_t *external_alloc(size_t bytes);

int caller(size_t n) {
    uint8_t *data = external_alloc(n);
    data[n - 1] = 7;
    data[0] = 7;
    free(data);
    return 7;
}
```

```click
verifying "an_extern_allocator_states_a_size_t_extent.c";

extern uint8_t* external_alloc(size_t bytes) {
    requires 0u64 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
    produces result[0..bytes];
}

int32 caller(size_t n) {
    requires 0u64 < n and n <= 100u64;
    ensures result == 7;
}
```

```expect
pass
```
