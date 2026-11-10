# A loop writes every element of a 64-bit block

A loop over a `size_t` index writes each element of a block with a 64-bit
extent. The loop keeps the block's wide range `p[0..n]` like any owned range;
the `allocation` token stays outside the loop, and `free` consumes both.

```c filename=a_loop_writes_every_element_of_a_64_bit_block.c
#include <stdlib.h>
#include <stdint.h>

int clear(size_t n) {
    uint32_t *p = malloc(n * sizeof(uint32_t));
    if (p == 0) {
        return 0;
    }
    for (size_t i = 0; i < n; i++) {
        p[i] = 0;
    }
    free(p);
    return 1;
}
```

```click
verifying "a_loop_writes_every_element_of_a_64_bit_block.c";

int32 clear(size_t n) {
    requires 1u64 <= n and n <= 100u64;
    ensures result == 0 or result == 1;
} by {
    step();
    step();
    branch {
        step_until(function.exit);
        solve();
    } else {}
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        owns p[0..n];
    }
    step_until(function.exit);
    solve();
}
```

```expect
pass
```
