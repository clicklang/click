# A signed 64-bit `allocation` byte count is refused

An `allocation` byte count is a 32-bit `int32` extent or a 64-bit `uint64`
(`size_t`) one. A `long` count is neither; it is stated through its
`size_t` conversion.

```c filename=a_signed_64_bit_allocation_byte_count_is_refused.c
#include <stdint.h>

uint8_t *external_alloc(long bytes);

int caller(void) {
    return 0;
}
```

```click
verifying "a_signed_64_bit_allocation_byte_count_is_refused.c";

extern uint8_t* external_alloc(int64 bytes) {
    requires 0 < bytes;
    ensures result != 0;
    produces allocation(result, bytes);
}

int32 caller() {
    ensures result == 0;
}
```

```expect
fail: resource `allocation` argument 1 expects int32 or uint64, got int64
```
