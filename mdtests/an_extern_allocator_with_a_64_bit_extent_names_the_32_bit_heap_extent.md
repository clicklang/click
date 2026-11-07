# An extern allocator with a 64-bit extent names the 32-bit heap extent

The byte count of `allocation(p, bytes)` is a heap block's extent, which Click
models as a checked 32-bit value. A `size_t` parameter used there directly is
refused with that reason and the spelling that is accepted:
`allocation(result, bytes as int32)` under a requirement that bounds `bytes`
(`mdtests/an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.md`).

```c filename=an_extern_allocator_with_a_64_bit_extent_names_the_32_bit_heap_extent.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint8_t *external_alloc(size_t bytes);

int caller(size_t n) {
    uint8_t *data = external_alloc(n);
    data[0] = 7;
    free(data);
    return 7;
}
```

```click
verifying "an_extern_allocator_with_a_64_bit_extent_names_the_32_bit_heap_extent.c";

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
fail: the byte count is a heap block's extent, which Click models as a checked 32-bit value
```
