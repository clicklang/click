# An extern `size_t` extent whose product may wrap is refused

`allocation(result, n * 4u64)` states a 64-bit extent of `n` four-byte
elements only when the product cannot have wrapped: the heap reads `n * 4u64`
bytes back as `n` elements. Wherever such a token is formed, here as the
caller assumes what the extern returns, the facts must decide
`1 <= n <= PTRDIFF_MAX / 4`. The caller bounds `n` below only, so the
returned token is refused.

```c filename=an_extern_size_t_extent_whose_product_may_wrap_is_refused.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint32_t *make(size_t n);

int caller(size_t n) {
    uint32_t *p = make(n);
    p[0] = 1;
    free(p);
    return 1;
}
```

```click
verifying "an_extern_size_t_extent_whose_product_may_wrap_is_refused.c";

extern uint32_t* make(size_t n) {
    requires 1u64 <= n;
    ensures result != 0;
    produces allocation(result, n * 4u64);
    produces uninitialized(result[0..n]);
}

int32 caller(size_t n) {
    requires 1u64 <= n;
    ensures result == 1;
}
```

```expect
fail: needs `1 <= n <= PTRDIFF_MAX / k`
```
