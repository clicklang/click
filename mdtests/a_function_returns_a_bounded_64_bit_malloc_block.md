# A function returns a bounded 64-bit `malloc` block

`make` returns `malloc(n * sizeof(uint32_t))` for a bounded `size_t` count,
a block with a 64-bit extent, possibly null. A resource that owns
`allocation(p, n * 4u64)` and `p[0..n]` when `p` is not null carries it to
the caller, which hands it to `dispose` to free. The token crosses both
calls: `make` produces it at its exit, and `dispose` consumes it.

```c filename=a_function_returns_a_bounded_64_bit_malloc_block.c
#include <stdint.h>
#include <stddef.h>
#include <stdlib.h>

uint32_t *make(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    return p;
}

void dispose(uint32_t *p, size_t n) {
    if (p != 0) {
        free(p);
    }
}

int caller(size_t n) {
    uint32_t *p = make(n);
    dispose(p, n);
    return 0;
}
```

```click
verifying "a_function_returns_a_bounded_64_bit_malloc_block.c";

resource buffer(p: uint32_t*, n: uint64) {
    if p != 0 {
        owns allocation(p, n * 4u64);
        owns p[0..n];
    }
}

uint32_t* make(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    produces buffer(result, n);
}

void dispose(uint32_t* p, size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    consumes buffer(p, n);
} by {
    if p != 0 { unfold(buffer(p, n)); step_until(function.exit); }
    else { unfold(buffer(p, n)); step_until(function.exit); }
}

int32 caller(size_t n) {
    requires 1u64 <= n and n <= 1000u64;
    ensures result == 0;
}
```

```expect
pass
```
