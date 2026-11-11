# A call naming a 64-bit extent with an unbounded count is refused

The caller owns a 64-bit block of `n` elements but passes a second count `k`
to a callee that consumes `allocation(p, n * 4u64)`. The requirement's
extent is decided at the call: `k` is unbounded, so `k * 4u64` may have
wrapped, and the call is refused before any token is compared.

```c filename=a_call_naming_a_64_bit_extent_with_an_unbounded_count_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

void release(uint32_t *p, size_t n) {
    free(p);
}

int caller(size_t n, size_t k) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    release(p, k);
    return 1;
}
```

```click
verifying "a_call_naming_a_64_bit_extent_with_an_unbounded_count_is_refused.c";

void release(uint32_t* p, size_t n) {
    consumes allocation(p, n * 4u64);
    consumes uninitialized(p[0..n]);
}

int32 caller(size_t n, size_t k) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0 or result == 1;
}
```

```expect
fail: resource `allocation` has a 64-bit byte count not proved to fit a heap block
```
