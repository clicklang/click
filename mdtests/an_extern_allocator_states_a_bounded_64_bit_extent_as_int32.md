# An extern allocator states a bounded 64-bit extent as `int32`

A heap block's extent is a checked 32-bit value. An allocator that takes a
`size_t` states its extent as `bytes as int32`, under a requirement that
bounds `bytes`, and a caller that meets the bound uses the storage.

```c filename=an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.c
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
verifying "an_extern_allocator_states_a_bounded_64_bit_extent_as_int32.c";

extern uint8_t* external_alloc(size_t bytes) {
    requires 0u64 < bytes and bytes <= 2147483647u64;
    ensures result != 0;
    produces allocation(result, bytes as int32);
    produces result[0..bytes as int32];
}

int32 caller(size_t n) {
    requires 0u64 < n and n <= 100u64;
    ensures result == 7;
}
```

```expect
pass
```
