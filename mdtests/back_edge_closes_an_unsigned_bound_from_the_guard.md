# The back edge closes an unsigned bound from the loop guard

After `i = i + 1` under the guard `i < n`, the invariant `i <= n` holds at
the back edge. For a `uint64` counter the signed arithmetic planner does not
apply, so the closer cites the loop's named premises, the guard among them,
in one `normalize() using` for the member. The `preserve` script needs no
`have i <= n;` restating it; here it is a single `step()`, and the back edge
closes implicitly.

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
    execute_until(loop(0));
    loop {
        decreases n - i;
        invariant i <= n;
        preserve by {
            step();
        }
    }
    execute();
}
```

```expect
pass
```
