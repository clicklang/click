# The back edge closes an unsigned bound from the loop guard

After `i = i + 1` under the guard `i < n`, the invariant `i <= n` holds at
the back edge. The guard proves that the increment fits in `uint64`. The
expanded proof applies `integer::uint64_increment_upper_bound` to the guard
at the recorded program point. The `maintain` script needs only the `step()`
that executes the increment.

```c filename=count.c
#include <stdint.h>
uint64_t count(uint64_t n) {
    uint64_t i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
```

```click
verifying "count.c";

uint64 count(uint64 n) {
    ensures result == n;
} by {
    step_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        maintain by {
            step();
        }
    }
}
```

```expect
pass
```
