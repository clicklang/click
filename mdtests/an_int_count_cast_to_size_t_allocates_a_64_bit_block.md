# An `int` count cast to `size_t` allocates a 64-bit block

The overflow-safe spelling `malloc((size_t)count * sizeof(int64_t))` with an
`int` count is a `size_t` product, so it makes a 64-bit block; the bounded
`count` proves it exact. The block is indexed with the `int` count.

```c filename=an_int_count_cast_to_size_t_allocates_a_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

int64_t last(int count) {
    int64_t *p = malloc((size_t)count * sizeof(int64_t));
    if (p == 0) {
        return 0;
    }
    p[count - 1] = 3;
    int64_t r = p[count - 1];
    free(p);
    return r;
}
```

```click
verifying "an_int_count_cast_to_size_t_allocates_a_64_bit_block.c";

int64_t last(int32 count) {
    requires 1 <= count and count <= 1000;
    ensures result == 0 or result == 3;
}
```

```expect
pass
```
