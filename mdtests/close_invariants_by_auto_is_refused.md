# `close_invariants by auto()` is refused with the form to write

`auto` has no script-tactic spelling, and the bare `close_invariants()` is
already a smart closer. `close_invariants by auto();` is therefore refused,
and the refusal names the forms that work instead of suggesting the
`by auto();` it was given.

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
            close_invariants by auto();
        }
    }
    execute();
}
```

```expect
fail: `close_invariants by auto()` is not a form: write `close_invariants();`, whose closer is already smart, or end the `preserve` script and let the back edge close implicitly
```
