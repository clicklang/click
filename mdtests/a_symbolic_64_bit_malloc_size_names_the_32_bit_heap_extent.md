# A symbolic 64-bit `malloc` size names the 32-bit heap extent

Click models a heap block with a checked 32-bit extent. A `size_t` size that
the facts do not fix to a constant cannot be narrowed into it yet, and an
upper bound on it is not enough. The refusal says so, rather than reporting a
type mismatch. The same holds for `calloc` and `realloc`.

```c filename=a_symbolic_64_bit_malloc_size_names_the_32_bit_heap_extent.c
#include <stdlib.h>
#include <stdint.h>

uint8_t *make(size_t n) {
    uint8_t *p = malloc(n);
    return p;
}
```

```click
verifying "a_symbolic_64_bit_malloc_size_names_the_32_bit_heap_extent.c";

uint8_t* make(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result != 0;
}
```

```expect
fail: heap allocation size must be a 32-bit value or a known constant
```
