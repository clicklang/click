# `close_invariants() by auto()` is refused with the form to write

`auto` is removed, and the bare `close_invariants()` is already a smart
closer. `close_invariants() by auto();` is therefore refused with the
removal's refusal, which says to delete the `by auto()`.

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
        preserve by {
            step();
            close_invariants() by auto();
        }
    }
}
```

```expect
fail: `auto()` is removed: a `by auto();` proof is the omitted proof, so delete it
```
