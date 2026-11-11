# A struct `calloc` with an `int` count allocates a 32-bit block

`calloc(n, sizeof(struct pair))` evaluates only its count, never the
product (`design/heap-extents.md`, stage 4). An `int` count makes a 32-bit
block of `n * 8` bytes once the facts prove `1 <= n <= INT32_MAX / 8`, and
its fields read as zero.

```c filename=a_struct_calloc_with_an_int_count_allocates_a_32_bit_block.c
#include <stdlib.h>
#include <stdint.h>

struct pair {
    uint8_t tag;
    int32_t value;
};

int make(int n) {
    struct pair *p = calloc(n, sizeof(struct pair));
    if (p == 0) {
        return 0;
    }
    int r = p->tag + p->value;
    free(p);
    return r;
}
```

```click
verifying "a_struct_calloc_with_an_int_count_allocates_a_32_bit_block.c";

int32 make(int32 n) {
    requires 1 <= n and n <= 100;
    ensures result == 0;
}
```

```expect
pass
```
